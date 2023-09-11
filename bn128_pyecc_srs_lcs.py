import random, time

from py_ecc.optimized_bn128 import (
    add as bn128_add,
    curve_order as bn128_order,
    G1 as bn128_G1,
    G2 as bn128_G2,
    b as bn128_b,
    b2 as bn128_b2,
    multiply as bn128_multiply,
    pairing as bn128_pairing,
    Z1 as bn128_Z1,
    Z2 as bn128_Z2,
    is_on_curve as bn128_is_on_curve
)

dp = bn128_order

n = 5
l = 2**n
nc = 5

print('message_length: ', l)
print('number of commitments: ', nc)


def fp_inv(a: int, p: int) -> int:
    # Extended euclidean algorithm to find modular inverses for integers
    a %= p
    if a == 0:
        return 0
    lm, hm = 1, 0
    low, high = a % p, p
    while low > 1:
        r = high // low
        nm, new = hm - lm * r, high - low * r
        lm, low, hm, high = nm, new, lm, low
    return lm %p

def fp_div(x, y, p:int):
    return x * fp_inv(y, p) % p

def fp_div_polys(a, b, p: int):
    """
    Long polynomial difivion for two polynomials in coefficient form
    """
    a = [x for x in a]
    o = []
    apos = len(a) - 1
    bpos = len(b) - 1
    diff = apos - bpos
    while diff >= 0:
        quot = fp_div(a[apos], b[bpos], p)
        o.insert(0, quot)
        for i in range(bpos, -1, -1):
            a[diff + i] -= b[i] * quot
        apos -= 1
        diff -= 1
    return [x % p for x in o]

def lagrange_polynomial(mdata: list, p: int):
    x_coords = [mdata[i][0] for i in range(len(mdata))]
    y_coords = [mdata[i][1] for i in range(len(mdata))]
    base_poly = [0]
    for i in range(len(x_coords)):
        basis = [1]
        for j in range(len(x_coords)):
            if j == i:
                continue
            basis = poly_mul_modp(basis, [-x_coords[j], 1], p)
            basis = poly_rmul_modp(basis, fp_inv(x_coords[i] - x_coords[j], p), p)
        base_poly = poly_add_modp(base_poly, poly_rmul_modp(basis, y_coords[i], p), p)
    return [coef %p for coef in base_poly]

def padding_zero(lst: list, itr: int):
    return [ lst[i] if i in range(len(lst)) else 0  for i in range(len(lst) + max(itr, 0)) ]

def poly_add_modp(poly_a: list, poly_b: list, p: int):
    difc = max(len(poly_a), len(poly_b)) - min(len(poly_a), len(poly_b))
    return [ i + j %p  for i, j in zip(padding_zero(poly_a, difc), padding_zero(poly_b, difc)) ]

def poly_minus_modp(poly_a: list, poly_b: list, p: int):
    difc = max(len(poly_a), len(poly_b)) - min(len(poly_a), len(poly_b))
    return [ i - j %p  for i, j in zip(padding_zero(poly_a, difc), padding_zero(poly_b, difc)) ]

def poly_rmul_modp(poly: list, a: int, p: int):
    return [(item*a)%p for item in poly]

def poly_mul_modp(poly_a: list, poly_b: list, p: int):
    prod = [0 for i in range(len(poly_a) + len(poly_b) - 1)]
    for i in range(len(poly_a)):
        for j in range(len(poly_b)):
            prod[i + j] += (poly_a[i]*poly_b[j])
    return [item%p for item in prod]

def poly_eval_modp(poly: list, r: int, p: int):
    r_pw = [r**i %p for i in range(len(poly))]
    return sum([(poly[i]*r_pw[i])%p for i in range(len(poly))])%p

def z_poly_modp(ind_list: list, p: int):
    zp = [1]
    for i in ind_list:
        zp = poly_mul_modp(zp, [-i, 1], p)
    return list(zp)

def z_inv_modp(ind_list: list, t: int, p: int):
    zp = [1]
    for i in range(t):
        if i in ind_list:
            continue
        zp = poly_mul_modp(zp, [-i, 1], p)
    return list(zp)

def ecp_sum(pl: list):
    pt_sum = bn128_Z1
    for pt in pl:
         pt_sum = bn128_add(pt_sum, pt) if bn128_is_on_curve(pt, bn128_b) else bn128_add(pt_sum, bn128_Z1)
    return pt_sum

def ecp_sum_twist(pl: list):
    pt_sum = bn128_Z2
    for pt in pl:
        pt_sum = bn128_add(pt_sum, pt) if bn128_is_on_curve(pt, bn128_b2) else bn128_add(pt_sum, bn128_Z2)
    return pt_sum

def gen_ranindlst(lngth: int, rnge: int):
    temp = set()
    while len(temp) < lngth:
        temp.add(random.randint(0, rnge-1))
    temlst = list(temp)
    temlst.sort()
    return temlst


##### Standard
def commit_srs(rl: list):
    dt_list =  [(i, rl[i]) for i in range(l)] 
    lag_coef = lagrange_polynomial(dt_list, dp)
    return ecp_sum([bn128_multiply(srs_1[i], lag_coef[i] ) for i in range(l)]), lag_coef

def batchprove_srs(rl: list, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    dt_list =  [(i, rl[i]) for i in range(l)]
    data_x, data_y, batch_size = dx, dy, len(dx)
    lag_coef = lagrange_polynomial(dt_list, dp)
    lp_coef = lagrange_polynomial([(data_x[i], data_y[i]) for i in range(batch_size) ], dp)

    pa = poly_add_modp(lag_coef, poly_rmul_modp(lp_coef, -1, dp), dp)
    zx_cofe = z_poly_modp(data_x, dp)
    qb_coef = fp_div_polys(pa, zx_cofe, dp)
    return ecp_sum([bn128_multiply(srs_1[i], qb_coef[i]) for i in range(len(qb_coef))])

def batchverifyeval_srs(C, P, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    data_x, data_y, batch_size = dx, dy, len(dx)
    m_data = [(data_x[i], data_y[i]) for i in range(batch_size)]

    lp_coef = lagrange_polynomial(m_data, dp)
    lp_coef_mp = [(-lp_coef[i])%dp for i in range(len(lp_coef))] # with neg coeff here
    zx_cofe = z_poly_modp(data_x, dp)

    lhs_lfpt = ecp_sum_twist( [bn128_multiply(srs_2[i], zx_cofe[i]) for i in range(len(zx_cofe))] )
    rhs_rtpt = ecp_sum( [bn128_multiply(srs_1[i], lp_coef_mp[i]) for i in range(len(lp_coef_mp))] )

    lhs_bnap = bn128_pairing(lhs_lfpt, P)
    rhs_bnap = bn128_pairing(srs_2[0], bn128_add(C, rhs_rtpt))
    return lhs_bnap == rhs_bnap


##### aggre-proof
### sect3 batch

gfp_12_one = bn128_pairing(bn128_G2, bn128_G1)/bn128_pairing(bn128_G2, bn128_G1)

def batchprove_s3(bp_list: list):
    aggre_bproof = ecp_sum([bn128_multiply(bp_list[i], gam_pw[i]) for i in range(nc)])
    return aggre_bproof

def batchverify_s3(c_list, abp, zinvbp_list, rxp_list):
    lhs_F = gfp_12_one
    for i in range(nc):
        lhs_F *= bn128_pairing(zinvbp_list[i], bn128_multiply(bn128_add(c_list[i], bn128_multiply(rxp_list[i], -1%dp) ) , gam_pw[i]))
    rhs = bn128_pairing(zt_p, abp)
    return lhs_F == rhs


### sect4, batchprove is combined with commit
def poly_sum_modp(poly_list: list, p: int):
    ps = [0]
    for poly_i in poly_list:
        ps = poly_add_modp(ps, poly_i, p)
    return ps

def batchprove_s4(rmplist: list, rxplist: list, rzlist: list, zbiplist: list, zbizlist: list):
    fx_i = [ poly_rmul_modp( poly_mul_modp(zbiplist[i], poly_minus_modp(rmplist[i], rxplist[i], dp), dp), gam_pw[i], dp ) for i in range(nc) ]
    f_x = poly_sum_modp(fx_i, dp)
    h_x = fp_div_polys(f_x, ztcf, dp)

    fz_xi = [ poly_rmul_modp(poly_minus_modp(rmplist[i], [rzlist[i]], dp), gam_pw[i] *zbizlist[i], dp) for i in range(nc) ]
    fz_x = poly_sum_modp(fz_xi, dp)
    L_x = poly_minus_modp(fz_x, poly_rmul_modp(h_x, z_tz, dp), dp)
    wp_x = fp_div_polys(L_x, [-r_z, 1], dp)
    
    W = ecp_sum([bn128_multiply( srs_1[i], h_x[i] ) for i in range(len(h_x))])
    F1 = ecp_sum([bn128_multiply( srs_1[i], fz_x[i] ) for i in range(len(fz_x))])
    Wp = ecp_sum([bn128_multiply( srs_1[i], wp_x[i] ) for i in range(len(wp_x))])
    F = bn128_add(F1, bn128_multiply(W, -z_tz %dp))
    return F, W, Wp #return W, Wp

def batchverify_s4(fin, wpin):
    return bn128_pairing(srs_2[0], fin) == bn128_pairing(bn128_add(srs_2[1], bn128_multiply(srs_2[0], -r_z %dp)), wpin)

# sect4.1: finalized one
def batchverify_s41(fin, wpin):
    fn = bn128_add(fin, bn128_multiply(wpin, r_z))
    return bn128_pairing(srs_2[0], fn) == bn128_pairing(srs_2[1], wpin)


###
setup_time_s = time.time()

tx = [i for i in range(l)]

r_pub = random.randint(1, dp-1)
rpb_pw = [ (r_pub**i)%dp for i in range(l)]

gam = random.randint(1, dp-1)
gam_pw = [ (gam**i)%dp for i in range(nc)]

srs_1 = [bn128_multiply(bn128_G1, rpb_pw[i]) for i in range(l)]
srs_2 = [bn128_multiply(bn128_G2, rpb_pw[i]) for i in range(l)]
srs_2.append(bn128_multiply(srs_2[-1], r_pub))

##### Data-indice-Input
rm_list = [[random.randint(0, dp-1) for i in range(l)] for j in range(nc)]
rsz_list = [random.randint(2, l-2) for i in range(nc)]
rib_list = [gen_ranindlst(rsz_list[i], l) for i in range(nc)]
rdb_list = [[rm_list[i][k] for k in rib_list[i]] for i in range(nc)]

setup_time_n = time.time()
print('setup time: ', setup_time_n - setup_time_s)

###
tts = time.time()

committing_list = [commit_srs(rm_list[i]) for i in range(nc)]
commitment_list = [committing_list[i][0] for i in range(nc)]
commitcoef_list = [committing_list[i][1] for i in range(nc)]
batchproof_list = [batchprove_srs(rm_list[i], rib_list[i], rdb_list[i]) for i in range(nc)] 

ttv = time.time()

batchverifyeval_srs(commitment_list[0], batchproof_list[0], rib_list[0], rdb_list[0])
tt=time.time()
print('One bn128 auto-batch opening verification ', tt-ttv)

###
ttm = time.time()
print('Commit-Prove list gen-time with scalability: ', ttv-tts)

rxd_list = [ [ (rib_list[i][j], rdb_list[i][j]) for j in range(rsz_list[i]) ] for i in range(nc) ]
rxcf_list = [ lagrange_polynomial(rxd_list[i], dp) for i in range(nc) ]
rxtp_list = [ ecp_sum([bn128_multiply(srs_1[j], rxcf_list[i][j]) for j in range(len(rxcf_list[i]))]) for i in range(nc) ]

ztcf = z_poly_modp([i for i in range(l)], dp)
zt_p = ecp_sum_twist([bn128_multiply(srs_2[i], ztcf[i]) for i in range(len(ztcf))])

zinvb_cflist = [ z_inv_modp(rib_list[i], l, dp) for i in range(nc) ]
zinvb_plist = [ ecp_sum_twist([ bn128_multiply(srs_2[j], zinvb_cflist[i][j]) for j in range(len(zinvb_cflist[i])) ]) for i in range(nc) ]

t0=time.time()
print('Setup on Sect3: ', t0-ttm)

abp_s3 = batchprove_s3(batchproof_list)
bvs3 = batchverify_s3(commitment_list, abp_s3, zinvb_plist, rxtp_list)
t01=time.time()

if bvs3:
    print('bn128 version aggre-proof sect3 batch-opening verified: ', t01-t0)

###
tst4 = time.time()

r_z = random.randint(3, 619)
rz_pw = [r_z**i %dp for i in range(l)]

z_tz = poly_eval_modp(ztcf, r_z, dp)

rmbd_list = [ [(a, b) for a, b in zip(rib_list[i], rdb_list[i])] for i in range(nc) ]
rxcf_list = [ lagrange_polynomial(rmbd_list[i], dp) for i in range(nc) ]
rz_list = [ poly_eval_modp(rxcf_list[i], r_z, dp) for i in range(nc) ]

zbinvp_list = [ z_inv_modp(rib_list[i], l, dp) for i in range(nc) ]
zbinvz_list = [ poly_eval_modp(zbinvp_list[i], r_z, dp) for i in range(nc) ]

ts4s = time.time()
print('Sect4 setup time: ', ts4s-tst4)

F, W, Wp = batchprove_s4(commitcoef_list, rxcf_list, rz_list, zbinvp_list, zbinvz_list)

ts4bp = time.time()
print('Sect 4 batchprove time: ', ts4bp-ts4s)

if batchverify_s4(F, Wp):
    print('bn128 version aggre-proof sect4 batch opening verified')
if batchverify_s41(F, Wp):
    print('bn128 version aggre-proof sect4.1 batch opening verified')

ts4n = time.time()
print('Sect 4 verification time: ', ts4n-ts4bp)

ttn = time.time()
print('Total execuation time: ', ttn-setup_time_s)