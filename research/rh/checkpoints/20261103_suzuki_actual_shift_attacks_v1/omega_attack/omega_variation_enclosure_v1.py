"""Arb enclosures for the actual Suzuki omega derivative at omega=1/2.

Finite source-normalized tests, with a proved geometric Lerch-series tail.
This is not a Lean proof, a global monotonicity theorem, or an RH certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def lerch_half(t, order, count):
    """Enclose sum_(j>=0) exp(-2jt)/(j+1/2)^order for exact t>0."""
    ratio = (-2*t).exp()
    require(0 < ratio < 1, 'geometric ratio not in (0,1)')
    power = arb(1)
    total = arb(0)
    for j in range(count):
        total += power/(arb(j)+arb(1)/2)**order
        power *= ratio
    tail = power/((arb(count)+arb(1)/2)**order*(1-ratio))
    # A symmetric ball is a conservative enclosure of the positive tail.
    return total+arb(0, tail.upper()), tail


def derivative_half(t, active_two, count):
    phi2, tail2 = lerch_half(t, 2, count)
    phi3, tail3 = lerch_half(t, 3, count)
    decay = (-t).exp()
    polar = -t**3/6-t*(1+decay)+2*(1-decay)
    arch = arb.pi()**2*t/8-arb(7)*arb(3).zeta()/4
    arch += decay*(t*phi2+phi3)/4
    prime = arb(0)
    if active_two:
        ln2 = arb(2).log()
        prime = ln2**2*(t-ln2)/2
    return polar+arch+prime, {'lerch2_tail_upper':str(tail2.upper()),
                             'lerch3_tail_upper':str(tail3.upper()),
                             'polar':str(polar), 'archimedean':str(arch),
                             'prime_two':str(prime)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision',type=int,default=256)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('OMEGA_VARIATION_RECEIPT.json'))
    parser.add_argument('--source-pdf',type=Path,default=Path(__file__).parents[1]/'primary_sources/SUZUKI_2206_03682v4.pdf')
    args = parser.parse_args()
    require(args.precision >= 128, 'precision must be at least 128 bits')
    require(not args.output.exists(), 'refusing to overwrite a receipt')
    source_hash = hashlib.sha256(args.source_pdf.read_bytes()).hexdigest()
    require(source_hash == 'eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41',
            'unexpected primary-source PDF')
    ctx.prec = args.precision
    ln2 = arb(2).log()
    ln3 = arb(3).log()
    count = 512
    points = [('1/10',arb(1)/10,False), ('1/2',arb(1)/2,False),
              ('log(2)-1/1000',ln2-arb(1)/1000,False),
              ('log(2)',ln2,True), ('log(2)+1/1000',ln2+arb(1)/1000,True)]
    rows = []
    for expression,t,active_two in points:
        require(0 < t < ln3, 'test outside the prime-2-only range')
        if not active_two:
            require(t < ln2, 'prime-free expression not proved below log(2)')
        elif expression != 'log(2)':
            require(ln2 < t, 'prime-2 expression not proved above log(2)')
        value,parts = derivative_half(t,active_two,count)
        require(value > 0, 'positive omega derivative not proved')
        rows.append({'t_exact_expression':expression,'t_enclosure':str(t),
                     'omega_exact':'1/2','d_omega_Psi_omega':str(value),
                     'positive':True,**parts})
    # One-sided t slopes of d_omega Psi_omega at the first activation.
    phi1,_ = lerch_half(ln2,1,count)
    phi2,_ = lerch_half(ln2,2,count)
    decay = (-ln2).exp()
    left = -ln2**2/2-1+(ln2+1)*decay+arb.pi()**2/8
    left -= decay*phi2/4+ln2*decay*phi1/2
    jump = ln2**2/2
    right = left+jump
    require(left < 0 < right, 'activation minimum in t was not proved')
    receipt = {'schema':'AEGIS_ACTUAL_SUZUKI_OMEGA_VARIATION_V1',
               'source_pdf_sha256':source_hash,
               'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'precision_bits':ctx.prec,'lerch_series_terms':count,
               'rounding':'python-flint Arb outward balls',
               'rows':rows,
               'first_activation':{'t_exact':'log(2)',
                  'd_t_d_omega_left':str(left),'d_t_d_omega_right':str(right),
                  'upward_jump_exact':'log(2)^2/2','upward_jump_enclosure':str(jump),
                  'strict_local_minimum_in_t':True},
               'proved_scope':'Finite actual-function positive omega derivatives at omega=1/2 and first-activation one-sided slopes.',
               'global_monotonicity_proven':False,'lean_kernel_replay':'NOT_RUN',
               'rh_proven':False}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
