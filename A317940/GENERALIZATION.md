# Generalization program after A317940

## Verified special case

The completed Lean proof treats

\[
\left(\prod_{r\ge0}(1+\tfrac12 z^{2^r})\right)^{1/2}.
\]

## General theorem suggested by the proof

For real or rational parameters \(0<q\le1\) and \(\alpha>0\), define the formal series

\[
F_{q,\alpha}(z)=\prod_{r\ge0}(1+qz^{2^r})^\alpha.
\]

Then every coefficient of \(F_{q,\alpha}\) is strictly positive.

For \(n=2^vm\), \(m\) odd,

\[
[z^n]\log F_{q,\alpha}
=\frac{\alpha}{m}\left(q^m-\sum_{j=1}^{v}\frac{q^{2^jm}}{2^j}\right)>0.
\]

The inequality follows from \(q^{2^jm}\le q^m\) and the strict finite bound
\(\sum_{j=1}^{v}2^{-j}<1\).

## Research questions

1. Determine the maximal parameter region in \((q,\alpha)\) for coefficientwise nonnegativity or positivity.
2. Replace the binary exponents \(2^r\) by \(b^r\) for integer bases \(b\ge2\).
3. Classify weight sequences \(w_r\) for which \(\prod_r(1+w_rz^{2^r})^\alpha\) has positive coefficients.
4. Translate these coefficient criteria into positivity theorems for Dirichlet roots of multiplicative functions.
5. Determine denominator and divisibility properties of the A317940 local coefficients.
6. Formalize the parameterized theorem in Lean over an ordered field.

## Strongest paper framing

The broader project is:

> A coefficient-positivity theorem for fractional powers of digital Euler products, with applications to Dirichlet roots of multiplicative functions and a Lean-verified resolution of OEIS A317940.

The parameterized theorem is presently a human proof and computationally tested consequence of the same argument; only the A317940 specialization has been fully formalized in Lean.
