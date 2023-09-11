import random, time

from py_ecc.optimized_bn128 import (
    add as bn128_add,
    curve_order as bn128_order,
    G1 as bn128_G1,
    G2 as bn128_G2,
    b as bn128_b,
    multiply as bn128_multiply,
    pairing as bn128_pairing,
    Z1 as bn128_Z1,
    is_on_curve as bn128_is_on_curve
)

d_p = bn128_order

n = 7
l = 2**n
nc = 10

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

def interpolate_eval_fast(dx: list, dy: list, m:int , p: int):
    f_ga = 0
    for j in range(len(dx)):
        coef_j = 1
        for m in range(len(dx)):
            if m == j:
                continue
            coef_j *= ((m-dx[m]) *fp_inv(dx[j]-dx[m], p))%p
        f_ga += (coef_j* dy[j])%p
    return f_ga%p

def poly_eval_modp(poly: list, r: int, p: int):
    return sum([(poly[i]*r**i)%p for i in range(len(poly))])%p

def poly_rmul_modp(poly: list, a: int, p: int):
    return [(item*a)%p for item in poly]

def poly_mul_modp(poly_a: list, poly_b: list, p: int):
    prod = [0 for i in range(len(poly_a) + len(poly_b) - 1)]
    for i in range(len(poly_a)):
        for j in range(len(poly_b)):
            prod[i + j] += (poly_a[i]*poly_b[j])
    return [item%p for item in prod]

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
        assert bn128_is_on_curve(pt, bn128_b)
        pt_sum = bn128_add(pt_sum, pt)
    return pt_sum

def gen_ranindlst(lngth: int, rnge: int):
    temp = set()
    while len(temp) < lngth:
        temp.add(random.randint(0, rnge-1))
    temlst = list(temp)
    temlst.sort()
    return temlst


setup_time_s = time.time()

tx = [i for i in range(l)]

r_pub = random.randint(1, d_p-1)
rpb_pw = [ (r_pub**i)%d_p for i in range(l)]

gam = random.randint(1, d_p-1)
gam_pw = [ (gam**i)%d_p for i in range(nc)]

##### Data-indice-Input
rm_list = [[random.randint(0, d_p-1) for i in range(l)] for j in range(nc)]
rsz_list = [random.randint(2, l-2) for i in range(nc)]
rib_list = [gen_ranindlst(rsz_list[i], l) for i in range(nc)]
rdb_list = [[rm_list[i][k] for k in rib_list[i]] for i in range(nc)]
rx_list = [sum([interpolate_eval_fast(rib_list[i], rdb_list[i], r_pub, d_p)])%d_p for i in range(nc)]

z_t = poly_eval_modp(z_poly_modp([i for i in range(l)], d_p), r_pub, d_p)
z_tp = bn128_multiply(bn128_G2, z_t)
zinvb_list = [poly_eval_modp(z_inv_modp(rib_list[i], l, d_p), r_pub, d_p) for i in range(nc)]

setup_time_n = time.time()
print('setup time: ', setup_time_n - setup_time_s)


##### Standard
def commit(rl: list):
    C = interpolate_eval_fast(tx, rl, r_pub, d_p)
    return bn128_multiply(bn128_G1, C)

def batchprove(rl: list, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    rlitpe = interpolate_eval_fast(tx, rl, r_pub, d_p)
    dlitpe = interpolate_eval_fast(dx, dy, r_pub, d_p)
    z_e = poly_eval_modp(z_poly_modp(dx, d_p), r_pub, d_p)
    batchpf = (rlitpe - dlitpe)*fp_inv(z_e, d_p) %d_p
    return bn128_multiply(bn128_G1, batchpf)

def batchverifyeval(C, P, dx: list, dy: list):
    assert len(dx) == len(dy) != 1
    dlitpe = interpolate_eval_fast(dx, dy, r_pub, d_p)
    z_e = poly_eval_modp(z_poly_modp(dx, d_p), r_pub, d_p)
    lhs_bnap = bn128_pairing(bn128_multiply(bn128_G2, z_e), P)
    rhs_bnap = bn128_pairing(bn128_G2, bn128_add(C, bn128_multiply(bn128_G1, (-dlitpe)%d_p)))
    return lhs_bnap == rhs_bnap


##### aggre-proof
### sect3 batch
def batchcommit_s3(c_list: list, ziblist: list):
    bcommit_eval_ag = ecp_sum([bn128_multiply(c_list[i], (gam_pw[i]*ziblist[i])%d_p) for i in range(nc)])
    return bcommit_eval_ag

def batchprove_s3(bp_list: list):
    aggre_bproof = ecp_sum([bn128_multiply(bp_list[i], gam_pw[i]) for i in range(nc)])
    return aggre_bproof

def batchverify_s3(abc, abp, ziblist: list, rxlist: list):
    bcommit_rx_ag = ecp_sum([bn128_multiply(bn128_G1, (gam_pw[i]*ziblist[i]*(-rxlist[i]))%d_p) for i in range(nc)])
    aggre_bcommit_eval = bn128_pairing(bn128_G2, bn128_add(abc,  bcommit_rx_ag))
    aggre_bproof_eval = bn128_pairing(z_tp, abp)
    return aggre_bproof_eval == aggre_bcommit_eval


# all based on bng1

tts = time.time()
commitment_list = [commit(rm_list[i]) for i in range(nc)]
batchproof_list = [batchprove(rm_list[i], rib_list[i], rdb_list[i]) for i in range(nc)] 

ttv = time.time()
batchverifyeval(commitment_list[0], batchproof_list[0], rib_list[0], rdb_list[0])
tt=time.time()
print('One BN128 auto-batch opening verification ', tt-ttv)

ttm = time.time()
print('Commit-Prove list gen-time with scalability: ', ttm-tts)

abc_s3 = batchcommit_s3(commitment_list, zinvb_list)
abp_s3 = batchprove_s3(batchproof_list)

tlcsp = time.time()
print('LCS prove-time: ', tlcsp-ttm)

if batchverify_s3(abc_s3, abp_s3, zinvb_list, rx_list):
    print('BN128 version aggre-proof sect3 batch opening verified')

ttn = time.time()
print('LCS verify-time: ', ttn-tlcsp)

print('Total execuation time: ', ttn-setup_time_s)