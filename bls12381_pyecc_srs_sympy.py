import time, random, sympy, numpy as np
from sympy import *
from sympy.abc import x

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
    neg as bls12381_neg
)

t_as = time.time()

n = 5
l = 2**n
nc = 2
d_p = bls12381_order
r_pub = random.randint(1, d_p-1)
#rpub_pow = [r_pub**i %d_p for i in range(l)]

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

def interpolate_eval_fast(dx: list, dy: list, gp: int, p: int):
    f_ga = 0
    for j in range(len(dx)):
        coef_j = 1
        for m in range(len(dx)):
            if m == j:
                continue
            coef_j *= ((gp-dx[m]) *fp_inv(dx[j]-dx[m], p)) %p
        f_ga += (coef_j* dy[j]) %p
    return f_ga %p

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
        base_poly = poly_add(base_poly, poly_rmul_modp(basis, int(y_coords[i]), p))
    return [coef%p for coef in base_poly]

def poly_eval_modp(poly: list, r: int, p: int):
    return sum([(poly[i]*r**i)%p for i in range(len(poly))])%p

def poly_add(poly_a: list, poly_b: list):
    return list( np.poly1d(poly_a[::-1])+np.poly1d(poly_b[::-1]) )[::-1]

def poly_rmul_modp(poly: list, a: int, p: int):
    return [(item*a)%p for item in poly]

def poly_mul(poly_a: list, poly_b: list):
    prod = [0 for i in range(len(poly_a) + len(poly_b) - 1)]
    for i in range(len(poly_a)):
        for j in range(len(poly_b)):
            prod[i + j] += (poly_a[i]*poly_b[j])
    return prod

def poly_mul_modp(poly_a: list, poly_b: list, p: int):
    prod = [0 for i in range(len(poly_a) + len(poly_b) - 1)]
    for i in range(len(poly_a)):
        for j in range(len(poly_b)):
            prod[i + j] += (poly_a[i]*poly_b[j])%p
    return [coef%p for coef in prod]

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

def ecp_sum2(pl: list):
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
    temlst.sort()
    return temlst

def int_bar(lst: list):
    return [int(lst[i]) for i in range(len(lst))]

def int_bar_modp(lst: list, p: int):
    return [int(lst[i])%p for i in range(len(lst))]


##### SRS Ver.
def commit_srs(rl: list):
    dt_list =  [(i, rl[i]) for i in range(l)]
    lag_coef = lagrange_polynomial(dt_list, d_p)
    return ecp_sum([bls12381_multiply(srs_1[i], lag_coef[i] ) for i in range(l)])

def prove_srs(rl: list, ind: int, da: int):
    dt_list =  [(i, rl[i]) for i in range(l)] 
    lag_coef = lagrange_polynomial(dt_list, d_p)

    quot = sympy.quo(sum([lag_coef[i]*x**i for i in range(l)])-da, x-ind).as_poly()
    quot_coef = quot.all_coeffs()[::-1]
    quot_coef_mp = [int(ZZ(quot_coef[i])%d_p) for i in range(len(quot_coef))]
    return ecp_sum([bls12381_multiply(srs_1[i], quot_coef_mp[i]) for i in range(len(quot_coef))])

def verify_srs(C, P, ind: int, da: int):
    lhs_bnopa = bls12381_pairing( bls12381_add(srs_2[1], bls12381_multiply(srs_2[0], (-ind)%d_p)), P )
    rhs_bnopa = bls12381_pairing( srs_2[0], bls12381_add(C, bls12381_multiply(srs_1[0], (-da)%d_p)) )
    return lhs_bnopa == rhs_bnopa

def Z(id_list: list):
    z_x = sympy.expand(sympy.prod([x - id_list[i] for i in range(len(id_list))]))
    return z_x

### batch-opening
def mbatchprove(rl: list, dx: list, dy: list):
    dt_list =  [(i, rl[i]) for i in range(l)] 
    lag_coef = lagrange_polynomial(dt_list, d_p)
    rp = sum([lag_coef[i]* x**i for i in range(len(rl))]).as_poly()

    assert len(dx) == len(dy) != 1
    data_x, data_y, batch_size = dx, dy, len(dx)
    lp_coef = lagrange_polynomial([(data_x[i], data_y[i]) for i in range(batch_size)], d_p)
    lp = sum([lp_coef[i]* x**i for i in range(batch_size)]).as_poly()

    z_x = Z(data_x).as_poly()

    q_batch = sympy.quo(rp - lp, z_x).as_poly()
    qb_coef = q_batch.all_coeffs()[::-1]
    qb_coef_mp = [int(ZZ(qb_coef[i]))%d_p for i in range(len(qb_coef))]
    pf_point = ecp_sum([bls12381_multiply(srs_1[i], qb_coef_mp[i]) for i in range(len(qb_coef_mp))])
    return pf_point

def mbatchverifyeval(C, P, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    data_x, data_y, batch_size = dx, dy, len(dx)
    m_data = [(data_x[i], data_y[i]) for i in range(batch_size)]

    lp_coef = lagrange_polynomial(m_data, d_p)
    lp_coef_mp = [(-lp_coef[i])%d_p for i in range(len(lp_coef))]
    # with neg coeff here

    zx_coef = Z(data_x).as_poly().all_coeffs()[::-1]
    zx_coef_mp = [int(ZZ(zx_coef[i]))%d_p for i in range(len(zx_coef))]

    lhs_lfpt = ecp_sum2( [bls12381_multiply(srs_2[i], zx_coef_mp[i]) for i in range(len(zx_coef_mp))] )
    rhs_rtpt = ecp_sum( [bls12381_multiply(srs_1[i], lp_coef_mp[i]) for i in range(len(lp_coef_mp))] )

    lhs_bnap = bls12381_pairing(lhs_lfpt, P)
    rhs_bnap = bls12381_pairing(srs_2[0], bls12381_add(C, rhs_rtpt))
    return lhs_bnap == rhs_bnap


#rfp_list = [random.randint(1, d_p-1) for _ in range(nc)]
#srs_1 = [bls12381_multiply(bls12381_G1, rfp_list[0])]
#srs_2 = [bls12381_multiply(bls12381_G2, rfp_list[1])]
srs_1 = [bls12381_G1]
srs_2 = [bls12381_G2]
for i in range(1, l):
    srs_1.append(bls12381_multiply(srs_1[-1], r_pub))
    srs_2.append(bls12381_multiply(srs_2[-1], r_pub))

true_count = 0
false_count = 0

for _ in range(10):
    ##### Standard
    setup_time_s = time.time()

    dtx = [i for i in range(l)]
    dty_list = [ [random.randint(1, d_p-1) for i in range(l)] for _ in range(nc)]

    rsz_list = [random.randint(2, l-1) for i in range(nc)]
    rib_list = gen_ranindlst(rsz_list[0], l)
    rdb_ped_list = [[dty_list[i][k] for k in rib_list] for i in range(nc)]


    setup_time_n = time.time()

    cm = commit_srs(dty_list[0])
    tn=time.time()
    j = random.randint(0, l-1)
    #pf = prove_srs(dty_list[0], j, dty_list[0][j])
    tpn=time.time()
    #print('mono-verify', verify_srs(cm, pf, j, dty_list[0][j]))
    tvn=time.time()
    mbpf = mbatchprove(dty_list[0], rib_list, rdb_ped_list[0])
    tt1=time.time()
    mbv = mbatchverifyeval(cm, mbpf, rib_list, rdb_ped_list[0])
    tt2=time.time()
    print('batch-verify: ', mbv)

    if mbv:
        true_count += 1
    else:
        false_count += 1
    if true_count > false_count +2:
        #print(r_pub, rfp_list[0], rfp_list[1])
        print(r_pub)

    print('batchprove time: ', tt1-tvn)
    print('batchverify time: ', tt2-tt1)
    '''
    print('setup_time: ', setup_time_n - setup_time_s)
    print('commit time: ', tn-setup_time_n)
    print('prove time: ', tpn-tn)
    print('verify time: ', tvn-tpn)
    '''

'''
##### Multi-Pedersen using default prime
def commit_arb(rs: int, rfp: int, rl: list):
    C = (rfp*interpolate_eval_fast(dtx, rl, rs, d_p)) %d_p
    return bls12381_multiply(bls12381_G1, C)

def batchprove_arb(rs: int, rfp: int, rl: list, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    rlitpe = interpolate_eval_fast(dtx, rl, rs, d_p)
    dlitpe = interpolate_eval_fast(dx, dy, rs, d_p)
    z_e = poly_eval_modp(z_poly_modp(dx, d_p), rs, d_p)
    batchpf = ((rfp*fp_inv(z_e, d_p))%d_p*(rlitpe - dlitpe)%d_p)%d_p
    return bls12381_multiply(bls12381_G1, batchpf)

def batchverifyeval_arb(rs: int, rfp: int, C, P, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    dlitpe = interpolate_eval_fast(dx, dy, rs, d_p)
    z_e = poly_eval_modp(z_poly_modp(dx, d_p), rs, d_p)
    lhs_bnap = bls12381_pairing(bls12381_multiply(bls12381_G2, z_e), P)
    rhs_bnap = bls12381_pairing(bls12381_G2, bls12381_add(C, bls12381_multiply(bls12381_G1, (-dlitpe*rfp)%d_p)))
    return lhs_bnap == rhs_bnap

def batchverifyeval_ped_arb(rs: int, rfpl: list, AC, AP, dx: list, y: list):
    assert len(rfpl) == len(y) != 1
    aggre_vec = ecp_sum( [ bls12381_multiply(bls12381_G1, -interpolate_eval_fast(dx, y[i], rs, d_p)*rfpl[i]%d_p)  for i in range(len(rfpl))] )
    z_e = poly_eval_modp(z_poly_modp(dx, d_p), rs, d_p)
    lhs_bnap = bls12381_pairing(bls12381_multiply(bls12381_G2, z_e), AP)
    rhs_bnap = bls12381_pairing(bls12381_G2, bls12381_add(AC, aggre_vec))
    return lhs_bnap==rhs_bnap

tsc = time.time()

commitment_list = [commit_arb(r_pub, rfp_list[i], dty_list[i]) for i in range(nc)]
batchproof_list = [batchprove_arb(r_pub, rfp_list[i], dty_list[i], rib_list, rdb_ped_list[i]) for i in range(nc)]

AGC = ecp_sum(commitment_list)
AGBP = ecp_sum(batchproof_list)

tscstup = time.time()
print('Pedersen Commit-Prove time: ', tscstup-tsc)

if batchverifyeval_ped_arb(r_pub, rfp_list, AGC, AGBP, rib_list, rdb_ped_list):
    print('bls12381 Pedersen auto_batch opening verified, arbitrary points and arbitrary number of commitments')

tvvv = time.time()
print('Pedersen verification time: ', tvvv-tscstup)
print('total execution time: ', tvvv-setup_time_s)

tsst=time.time()
for i in range(nc):
    batchverifyeval_arb(r_pub, rfp_list[i], commitment_list[i], batchproof_list[i], rib_list, rdb_ped_list[i])
tnnt=time.time()
print('Individual verification time: ', tnnt-tsst)
'''