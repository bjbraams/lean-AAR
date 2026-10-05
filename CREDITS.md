# Credits and related upstream work

The project formalizes material from Andrews, Askey and Roy, *Special Functions*
(1999), and the NIST Digital Library of Mathematical Functions, using Mathlib.
Existing module copyright and authorship notices remain authoritative.

## TauCeti

TauCeti is available as a dependency at revision
`a780c7ad6beb23f60a17351a492d177878020ad5`. The source headers of the modules below
credit **The Tau Ceti contributors**, under the Apache 2.0 license.

The [reuse review and implementation](TauCetiReview.md) records six adopted uses.
Three existing proofs now call TauCeti, new bridges connect the real restrictions
of the complex error functions, and three admissions (two Hermite Fourier
identities and compact-support Parseval) have been replaced by checked proofs.
The affected module headers also credit the imported work.

- [Hermite orthogonality](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean):
  `integral_hermite_mul_hermite_mul_gaussian`, now used for AAR's
  probabilists’ Hermite orthogonality proof.
- [Polynomial Gaussian integrability](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Gaussian/PolynomialMemLp.lean):
  `integrable_eval_mul_exp_neg_sq`, now used for the matching AAR helper.
- [Beta integrals](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean):
  `integral_rpow_mul_one_sub_rpow`, now used for AAR's real beta integral.
- [Error function](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Erf.lean):
  the real `erf` and `erfc` APIs, identified with AAR's complex functions on real inputs.
- [Hermite Fourier transform](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/Basic.lean):
  `fourier_twoPiHermiteFunction` supplies the upstream eigenfunction theorem for
  the now-proved `hermitePhys_fourier_eigenfunction` and `hermite_fourier_eigenfunction`.
  Local adapters account for the Fourier phase, dilation and polynomial normalization.
- [Polynomial completeness](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/InnerProductSpace/PolynomialCompleteness.lean)
  and [weighted orthogonal bases](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/InnerProductSpace/WeightedOrthogonalBasis.lean):
  the completeness and basis construction used to prove
  `orthogonal_polynomials_parseval`, followed by Mathlib’s Hilbert-basis Parseval identity.

- [Hermite parity](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Polynomial/Hermite/Derivative.lean):
  `Polynomial.hermite_aeval_neg`, and the Gaussian integrability
  `integrable_aeval_mul_gaussian` from the Hermite orthogonality module above. Both are
  used for the now-proved `hermite_even_cosine_transform` and `hermite_odd_sine_transform`
  in [Integrals.lean](AAR/OrthogonalPolynomials/Integrals.lean).

Related real incomplete-gamma, Dirichlet and multivariate-Gamma developments are
not replacements for AAR's general complex statements. Adoption should retain
attribution in the affected module headers and at the point of use.
