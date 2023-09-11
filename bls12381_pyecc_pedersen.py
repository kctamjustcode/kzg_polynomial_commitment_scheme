import time, random

from py_ecc.optimized_bls12_381 import (
    add as bls12381_add,
    curve_order as bls12381_order,
    G1 as bls12381_G1,
    G2 as bls12381_G2,
    b as bls12381_b,
    multiply as bls12381_multiply,
    pairing as bls12381_pairing,
    Z1 as bls12381_Z1,
    is_on_curve as bls12381_is_on_curve
)

t_as = time.time()

n = 7
l = 2**n
nc = 10
d_p = bls12381_order
r_pub = random.randint(1, d_p-1)

print('length: ', l)
print('number of commitments ', nc)


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

def poly_eval_modp(poly: list, r: int, p: int):
    return sum([(poly[i]*r**i)%p for i in range(len(poly))])%p

def poly_rmul_modp(poly: list, a: int, p: int):
    return [(item*a)%p for item in poly]

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

def gen_ranindlst(lngth: int, rnge: int):
    temp = set()
    while len(temp) < lngth:
        temp.add(random.randint(0, rnge-1))
    temlst = list(temp)
    temlst.sort()
    return temlst


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


##### Standard upto Pedersen
setup_time_s = time.time()

rfp_list = [random.randint(1, d_p-1) for _ in range(nc)]

dtx = [i for i in range(l)]
dty_list = [ [random.randint(1, d_p-1) for i in range(l)] for _ in range(nc)]

rsz_list = [random.randint(2, l-1) for i in range(nc)]
rib_list = gen_ranindlst(rsz_list[0], l)
rdb_ped_list = [[dty_list[i][k] for k in rib_list] for i in range(nc)]

setup_time_n = time.time()
print('setup_time: ', setup_time_n - setup_time_s)


tsc = time.time()
commitment_list = [commit_arb(r_pub, rfp_list[i], dty_list[i]) for i in range(nc)]
batchproof_list = [batchprove_arb(r_pub, rfp_list[i], dty_list[i], rib_list, rdb_ped_list[i]) for i in range(nc)]

AGC = ecp_sum(commitment_list)
AGBP = ecp_sum(batchproof_list)

tscstup = time.time()
print('Pedersen Commit-Prove time: ', tscstup-tsc)

if batchverifyeval_ped_arb(r_pub, rfp_list, AGC, AGBP, rib_list, rdb_ped_list):
    print('BLS12381 Pedersen auto_batch opening verified, arbitrary points and arbitrary number of commitments')

tvvv = time.time()
print('Pedersen verification time: ', tvvv-tscstup)
print('total execution time: ', tvvv-setup_time_s)

tsst=time.time()
for i in range(nc):
    batchverifyeval_arb(r_pub, rfp_list[i], commitment_list[i], batchproof_list[i], rib_list, rdb_ped_list[i])
tnnt=time.time()
print('Individual verification time: ', tnnt-tsst)
