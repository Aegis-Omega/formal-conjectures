"""Two evaluations of the derivative of Suzuki (2206.03682v4), (1.1).

This checks a source-normalization discrepancy. It is not an RH certificate.
Arb arithmetic is used only after the analytic derivative is derived on paper.
No root-finding or quadrature is used to decide the signs.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('source_pdf', type=Path)
    parser.add_argument('receipt', type=Path)
    args = parser.parse_args()
    require(not args.receipt.exists(), 'refusing to overwrite a receipt')
    pdf = args.source_pdf.read_bytes()
    require(hashlib.sha256(pdf).hexdigest() ==
            'eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41',
            'unexpected primary PDF bytes')
    ctx.prec = 300
    pi = arb.pi()
    psi = (arb(1) / 4).digamma()
    # Euler's constant obtained independently from psi(1)=-gamma.
    gamma = -arb(1).digamma()
    c_printed = pi / 4 - (gamma + 3 * arb(2).log()) / 2
    offset = pi.log() / 2
    require(arb(57)/100 < offset < arb(58)/100, 'offset not isolated')
    rows = []
    for numerator, denominator in [(1, 8), (1, 3), (1, 2)]:
        t = arb(numerator) / denominator
        require(0 < t < arb(2).log(), 'test point outside prime-free interval')
        x = (-t/2).exp()
        polar = 2 * ((t/2).exp() - x)
        closed = polar + (psi-pi.log())/2 + x.atan() + x.atanh()
        printed = polar + c_printed - (t/2).exp().atan() + x.atanh()
        # Differentiating the convergent Lerch series gives
        # 2 sum_{j>=0} x^(4j+1)/(4j+1). All terms are positive here.
        count = 512
        power = x
        ratio = x**4
        partial = arb(0)
        for j in range(count):
            partial += 2 * power / (4*j+1)
            power *= ratio
        tail_upper = 2 * power / ((4*count+1)*(1-ratio))
        series_interval = partial + arb(0, tail_upper.upper())
        from_series = polar + (psi-pi.log())/2 + series_interval
        require((closed-from_series).contains(0), 'derivative evaluations disagree')
        require((printed-closed-offset).contains(0), 'printed offset mismatch')
        # At t=1/3, the formula literally printed in §4.1 has the wrong sign.
        if (numerator, denominator) == (1, 3):
            require(closed < 0 and printed > 0, 'expected sign separation not certified')
        rows.append({'t':[numerator,denominator],
                     'derivative_from_definition':str(closed),
                     'derivative_from_lerch_series':str(from_series),
                     'printed_derivative':str(printed),
                     'printed_minus_correct':str(printed-closed),
                     'series_terms':count,'series_tail_upper':str(tail_upper)})
    receipt = {
        'schema':'AEGIS_SUZUKI_NORMALIZATION_AUDIT_V1',
        'precision_bits':ctx.prec,
        'source_pdf_sha256':hashlib.sha256(pdf).hexdigest(),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'rounding':'python-flint Arb outward balls',
        'analytic_scope':'derivative of (1.1) for 0<t<log(2); finite numerical cross-check',
        'offset':'log(pi)/2',
        'offset_ball':str(offset),
        'rows':rows,
        'rh_proven':False,
        'lean_kernel_replay':'NOT_RUN',
        'independent_person_review':'NOT_RUN',
        'shared_interval_library':True,
    }
    args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
