import time, random

from py_ecc.optimized_bls12_381 import (
    add as bls12381_add,
    curve_order as bls12381_order,
    G1 as bls12381_G1,
    G2 as bls12381_G2,
    b as bls12381_b,
    b2 as bls12381_b2,
    multiply as bls12381_multiply,
    pairing as bls12381_pairing,
    Z1 as bls12381_Z1,
    Z2 as bls12381_Z2,
    is_on_curve as bls12381_is_on_curve,
)

t_as = time.time()

n = 4
l = 2**n
nc = 10
d_p = bls12381_order
r_pub = random.randint(1, d_p-1)

print('length: ', l)
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
    return lm % p

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
        base_poly = poly_add(base_poly, poly_rmul_modp(basis, y_coords[i], p))
    return [coef %p for coef in base_poly]

def padding_zero(lst: list, itr: int):
    return [ lst[i] if i in range(len(lst)) else 0  for i in range(len(lst) + max(itr, 0)) ]

def poly_add(poly_a: list, poly_b: list):
    difc = max(len(poly_a), len(poly_b)) - min(len(poly_a), len(poly_b))
    return [ i + j for i, j in zip(padding_zero(poly_a, difc), padding_zero(poly_b, difc)) ]

def poly_eval_modp(poly: list, r: int, p: int):
    return sum([(poly[i]*(r**i)%p)%p for i in range(len(poly))])%p

def poly_rmul_modp(poly: list, a: int, p: int):
    return [(item*a)%p for item in poly]

def poly_mul_modp(poly_a: list, poly_b: list, p: int):
    prod = [0 for i in range(len(poly_a) + len(poly_b) - 1)]
    for i in range(len(poly_a)):
        for j in range(len(poly_b)):
            prod[i + j] += (poly_a[i]*poly_b[j])%p
    return [coef %p for coef in prod]

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
    pt_sum = bls12381_Z1
    for pt in pl:
        assert bls12381_is_on_curve(pt, bls12381_b)
        pt_sum = bls12381_add(pt_sum, pt)
    return pt_sum

def ecp_sum_twist(pl: list):
    pt_sum = bls12381_Z2
    for pt in pl:
        assert bls12381_is_on_curve(pt, bls12381_b2)
        pt_sum = bls12381_add(pt_sum, pt)
    return pt_sum

def gen_ranindlst(lngth: int, rnge: int):
    temp = set()
    while len(temp) < lngth:
        temp.add(random.randint(0, rnge-1))
    temlst = list(temp)
    #temlst.sort()
    return temlst


##### SRS Ver.
def commit_srs(rl: list):
    dt_list =  [(i, rl[i]) for i in range(l)]
    lag_coef = lagrange_polynomial(dt_list, d_p)
    return ecp_sum([bls12381_multiply(srs_1[i], lag_coef[i] ) for i in range(l)])

def prove_srs(rl: list, ind: int, da: int):
    dt_list =  [(i, rl[i]) for i in range(l)] 
    lag_coef = lagrange_polynomial(dt_list, d_p)
    quot = fp_div_polys(lag_coef, [-ind, 1], d_p)
    return ecp_sum([bls12381_multiply(srs_1[i], quot[i]) for i in range(len(quot))])

def verify_srs(C, P, ind: int, da: int):
    lhs_bnopa = bls12381_pairing( bls12381_add(srs_2[1], bls12381_multiply(srs_2[0], (-ind)%d_p)), P )
    rhs_bnopa = bls12381_pairing( srs_2[0], bls12381_add(C, bls12381_multiply(srs_1[0], (-da)%d_p)) )
    return lhs_bnopa == rhs_bnopa

### batch-opening
def batchprove_srs(rl: list, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    dt_list =  [(i, rl[i]) for i in range(l)]
    data_x, data_y, batch_size = dx, dy, len(dx)
    lag_coef = lagrange_polynomial(dt_list, d_p)
    lp_coef = lagrange_polynomial([(data_x[i], data_y[i]) for i in range(batch_size)], d_p)

    pa = poly_add(lag_coef, poly_rmul_modp(lp_coef, -1, d_p))
    zx_cofe = z_poly_modp(data_x, d_p)
    qb_coef = fp_div_polys(pa, zx_cofe, d_p)
    return ecp_sum([bls12381_multiply(srs_1[i], qb_coef[i]) for i in range(len(qb_coef))])

def batchverifyeval_srs(C, P, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    data_x, data_y, batch_size = dx, dy, len(dx)
    m_data = [(data_x[i], data_y[i]) for i in range(batch_size)]

    lp_coef = lagrange_polynomial(m_data, d_p)
    lp_coef_mp = [(-lp_coef[i])%d_p for i in range(len(lp_coef))] # with neg coeff here
    zx_cofe = z_poly_modp(data_x, d_p)

    lhs_lfpt = ecp_sum_twist( [bls12381_multiply(srs_2[i], zx_cofe[i]) for i in range(len(zx_cofe))] )
    rhs_rtpt = ecp_sum( [bls12381_multiply(srs_1[i], lp_coef_mp[i]) for i in range(len(lp_coef_mp))] )

    lhs_bnap = bls12381_pairing(lhs_lfpt, P)
    rhs_bnap = bls12381_pairing(srs_2[0], bls12381_add(C, rhs_rtpt))
    return lhs_bnap == rhs_bnap

tsrs=time.time()
rpb_pw = [r_pub**i %d_p for i in range(l)]
srs_1 = [bls12381_multiply(bls12381_G1, rpb_pw[i]) for i in range(l)]
srs_2 = [bls12381_multiply(bls12381_G2, rpb_pw[i]) for i in range(l)]
tsrsn=time.time()
print('SRS: ', tsrsn-tsrs)

def batchverifyeval_ped_srs(AC, AP, dx: list, rdb: list):   # rfp_list is 'missing'
    data_list = [[(dx[i], rdb[j][i]) for i in range(len(dx))] for j in range(nc)]
    lag_list = [lagrange_polynomial(data_list[i], d_p) for i in range(nc)]
    aggre_vec = ecp_sum([ecp_sum([bls12381_multiply(srs_1[i], (-lag_list[j][i])%d_p) for i in range(len(lag_list[j]))]) for j in range(nc)])
    zx_cofe = z_poly_modp(dx, d_p)

    lhs_lfpt = ecp_sum_twist([bls12381_multiply(srs_2[i], zx_cofe[i]) for i in range(len(zx_cofe))])
    lhs_bnap = bls12381_pairing(lhs_lfpt, AP)
    rhs_bnap = bls12381_pairing(srs_2[0], bls12381_add(AC, aggre_vec))
    return lhs_bnap==rhs_bnap


dtx = [i for i in range(l)]
dty_list = [ [random.randint(1, d_p-1) for i in range(l)] for _ in range(nc)]

rsz_list = [random.randint(2, l-1) for i in range(nc)]
rib_list = gen_ranindlst(rsz_list[0], l)
rdb_ped_list = [[dty_list[i][k] for k in rib_list] for i in range(nc)]

tscstup = time.time()

commitment_list = [commit_srs(dty_list[i]) for i in range(nc)]
batchproof_list = [batchprove_srs(dty_list[i], rib_list, rdb_ped_list[i]) for i in range(nc)]

tcb=time.time()
print('Pedersen Commit-Prove time: ', tcb-tscstup)

AGC = ecp_sum(commitment_list)
AGBP = ecp_sum(batchproof_list)

bpv=batchverifyeval_ped_srs(AGC, AGBP, rib_list, rdb_ped_list)
if bpv:
    print('bls12381 Pedersen auto_batch opening verified, arbitrary points and arbitrary number of commitments')
tnnn=time.time()
print('Pedersen Verify time: ', tcb-tscstup)

tiv=time.time()
for i in range(nc):
    batchverifyeval_srs(commitment_list[i], batchproof_list[i], rib_list, rdb_ped_list[i])
tivn=time.time()
print('ind. ver. time: ', tivn-tiv)
