/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic

/-!
# q-Appell functions and their transformations (DLMF §§17.4(iii),17.11)

All four functions use the actual double series. Their bidisc convergence is
asserted separately, so totalized `tsum` is never used to claim continuation.
The transformations state a common convergence region and all lower-parameter
exclusions. Products reuse the existing q-Pochhammer symbols.
-/

@[expose] public noncomputable section
open Complex Finset
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- One double-series term of the first q-Appell function. -/
def qAppell1Term (a b bp c q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammer a q (p.1+p.2) * qPochhammer b q p.1 * qPochhammer bp q p.2 *
    x^p.1 * y^p.2 /
    (qPochhammer q q p.1 * qPochhammer q q p.2 * qPochhammer c q (p.1+p.2))
/-- The first q-Appell function, totalized outside its double-series convergence set. -/
@[dlmf 17.4.E5]
def qAppell1 (a b bp c q x y : ℂ) : ℂ := ∑' p : ℕ × ℕ, qAppell1Term a b bp c q x y p

/-- One double-series term of the second q-Appell function. -/
def qAppell2Term (a b bp c cp q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammer a q (p.1+p.2) * qPochhammer b q p.1 * qPochhammer bp q p.2 *
    x^p.1 * y^p.2 /
    (qPochhammerList [q,c] q p.1 * qPochhammerList [q,cp] q p.2)
/-- The second q-Appell function. -/
@[dlmf 17.4.E6]
def qAppell2 (a b bp c cp q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell2Term a b bp c cp q x y p

/-- One double-series term of the third q-Appell function. -/
def qAppell3Term (a ap b bp c q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammerList [a,b] q p.1 * qPochhammerList [ap,bp] q p.2 * x^p.1 * y^p.2 /
    (qPochhammer q q p.1 * qPochhammer q q p.2 * qPochhammer c q (p.1+p.2))
/-- The third q-Appell function. -/
@[dlmf 17.4.E7]
def qAppell3 (a ap b bp c q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell3Term a ap b bp c q x y p

/-- One double-series term of the fourth q-Appell function. -/
def qAppell4Term (a b c cp q x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  qPochhammerList [a,b] q (p.1+p.2) * x^p.1 * y^p.2 /
    (qPochhammerList [q,c] q p.1 * qPochhammerList [q,cp] q p.2)
/-- The fourth q-Appell function. -/
@[dlmf 17.4.E8]
def qAppell4 (a b c cp q x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, qAppell4Term a b c cp q x y p

/-- All four q-Appell double series converge absolutely on the stated bidisc. -/
@[dlmf 17.4.iii]
theorem summable_qAppell (a ap b bp c cp q x y : ℂ) (hq : ‖q‖<1)
    (hc : qDenominatorRegular [c,cp] q) (hx : ‖x‖<1) (hy : ‖y‖<1) :
    Summable (qAppell1Term a b bp c q x y) ∧
    Summable (qAppell2Term a b bp c cp q x y) ∧
    Summable (qAppell3Term a ap b bp c q x y) ∧
    Summable (qAppell4Term a b c cp q x y) := by
  sorry

/-- Reduction of the first q-Appell function to a 3-phi-2. -/
@[dlmf 17.11.E1]
theorem qAppell1_transformation (a b bp c q x y : ℂ)
    (hq : ‖q‖<1) (ha0 : a≠0) (ha : ‖a‖<1) (hx : ‖x‖<1) (hy : ‖y‖<1)
    (hc : qDenominatorRegular [c,b*x,bp*y] q) :
    qAppell1 a b bp c q x y =
      qPochhammerListInf [a,b*x,bp*y] q / qPochhammerListInf [c,x,y] q *
        qPhi [c/a,x,y] [b*x,bp*y] q a := by
  sorry

/-- Transformation of the second q-Appell function to a normally convergent double series. -/
@[dlmf 17.11.E2]
theorem qAppell2_transformation (a b bp c cp q x y : ℂ)
    (hq : ‖q‖<1) (hb0 : b≠0) (hb : ‖b‖<1) (hx : ‖x‖<1) (hy : ‖y‖<1)
    (hc : qDenominatorRegular [c,cp,a*x] q) :
    qAppell2 a b bp c cp q x y =
      qPochhammerListInf [b,a*x] q / qPochhammerListInf [c,x] q *
        ∑' p : ℕ × ℕ,
          qPochhammerList [a,bp] q p.1 * qPochhammerList [c/b,x] q p.2 *
            b^p.2 * y^p.1 /
            (qPochhammerList [q,cp] q p.1 * qPochhammer q q p.2 *
              qPochhammer (a*x) q (p.1+p.2)) := by
  sorry

/-- Transformation of the third q-Appell function. -/
@[dlmf 17.11.E3]
theorem qAppell3_transformation (a ap b bp c q x y : ℂ)
    (hq : ‖q‖<1) (ha0 : a≠0) (ha : ‖a‖<1) (hx : ‖x‖<1) (hy : ‖y‖<1)
    (hc : qDenominatorRegular [c,c/a,b*x] q) :
    qAppell3 a ap b bp c q x y =
      qPochhammerListInf [a,b*x] q / qPochhammerListInf [c,x] q *
        ∑' p : ℕ × ℕ,
          qPochhammerList [ap,bp] q p.1 * qPochhammer x q p.2 *
            qPochhammer (c/a) q (p.1+p.2) * a^p.2 * y^p.1 /
            (qPochhammerList [q,c/a] q p.1 * qPochhammerList [q,b*x] q p.2) := by
  sorry

/-- The multivariate series generalizing the first q-Appell function. -/
def qLauricellaTerm (n : ℕ) (a c q : ℂ) (b x : Fin n → ℂ) (m : Fin n → ℕ) : ℂ :=
  qPochhammer a q (∑ i, m i) * (∏ i, qPochhammer (b i) q (m i) * x i ^ m i) /
    ((∏ i, qPochhammer q q (m i)) * qPochhammer c q (∑ i, m i))

/-- Absolute convergence of the multivariate Appell generalization. -/
@[dlmf 17.11.E4]
theorem summable_qLauricella (n : ℕ) (a c q : ℂ) (b x : Fin n → ℂ)
    (hq : ‖q‖<1) (hc : qDenominatorRegular [c] q) (hx : ∀ i, ‖x i‖<1) :
    Summable (qLauricellaTerm n a c q b x) := by
  sorry

/-- The full n-variable generalization, including the empty-variable case. -/
@[dlmf 17.11.E4]
theorem qLauricella_transformation (n : ℕ) (a c q : ℂ) (b x : Fin n → ℂ)
    (hq : ‖q‖<1) (ha0 : a≠0) (ha : ‖a‖<1) (hx : ∀ i, ‖x i‖<1)
    (hc : qDenominatorRegular (c :: List.ofFn (fun i => b i*x i)) q) :
    (∑' m : Fin n → ℕ, qLauricellaTerm n a c q b x m) =
      qPochhammerListInf (a :: List.ofFn (fun i => b i*x i)) q /
        qPochhammerListInf (c :: List.ofFn x) q *
          qPhi ((c/a) :: List.ofFn x) (List.ofFn (fun i => b i*x i)) q a := by
  sorry

/-- The multivariate q-Appell coefficient at two variables is the first q-Appell coefficient. -/
@[dlmf 17.11]
theorem qLauricellaTerm_two (a b bp c q x y : ℂ) (m : Fin 2 → ℕ) :
    qLauricellaTerm 2 a c q ![b,bp] ![x,y] m =
      qAppell1Term a b bp c q x y (m 0,m 1) := by
  simp [qLauricellaTerm,qAppell1Term,Fin.sum_univ_two,Fin.prod_univ_two]
  ring

/-- DLMF17.11p2: the multivariate transformation specializes to the first q-Appell series
when n=2. Reindexing holds even for totalized series; convergence hypotheses are unchanged. -/
@[dlmf 17.11]
theorem qLauricella_two (a b bp c q x y : ℂ) :
    (∑' m : Fin 2 → ℕ, qLauricellaTerm 2 a c q ![b,bp] ![x,y] m) =
      qAppell1 a b bp c q x y := by
  calc
    (∑' m : Fin 2 → ℕ, qLauricellaTerm 2 a c q ![b,bp] ![x,y] m)
        = ∑' m : Fin 2 → ℕ, qAppell1Term a b bp c q x y (m 0,m 1) :=
          tsum_congr (qLauricellaTerm_two a b bp c q x y)
    _ = ∑' p : ℕ × ℕ, qAppell1Term a b bp c q x y p :=
          (finTwoArrowEquiv ℕ).tsum_eq _
    _ = qAppell1 a b bp c q x y := rfl

end DLMF.QHypergeometric
