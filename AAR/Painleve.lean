/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Painleve.Basic
public import AAR.Painleve.Backlund
public import AAR.Painleve.Airy
public import AAR.Painleve.LaxPair
public import AAR.Painleve.Rational
public import AAR.Painleve.LocalTheory
public import AAR.Painleve.Poles
public import AAR.Painleve.Tau

/-! # Painlevé transcendents, following Beals–Wong Chapter 15

The parameter convention is `u'' = 2u³ + xu - c` for `PII(c)`.

This development proves local real existence and uniqueness, the Bäcklund reflection
and integer shifts, rational solutions for every integer parameter, and meromorphic
Airy-based solutions for every half-integer parameter. It also proves the Lax
compatibility calculation, the energy derivative, a tau-quotient converse, and simple
pole/residue restrictions for solutions already known to be meromorphic.

The rational classification converse and uniqueness, global meromorphic continuation
of arbitrary solutions, Stokes/isomonodromy theory, and the real connection formulas
of Beals–Wong §15.8 are not yet formalized. The Airy scale satisfies `k³ = -1/2`;
this corrects the substitution printed on page 407.
-/
