import Holant.Proofs.Closure.ClosureExoticFiberCounts

/-! Actual cross cards preserve every live tomographic row. Support counting
is applied only to that proper PairSafe output. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
open scoped BigOperators
open Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

def crossed (M : Matching P r) (e f : Fin r) :
    Matching (Remaining (M.ports (e,true)) (M.ports (f,false)))
      (Fintype.card (OtherEdges f)) :=
  ⟨(Equiv.prodCongr (edgeEnum f) (Equiv.refl Bool)).trans (splicePorts M.ports e f)⟩

def crossLabel (labels : Label → Fin r → Label) (e f : Fin r) (k a : Label)
    (d : OtherEdges f) : Label :=
  if d.val = e then MatchingCard.spliceLabel (labels a e) k (labels a f) else labels a d.val

def crossLabels (labels : Label → Fin r → Label) (e f : Fin r) (k a : Label)
    (j : Fin (Fintype.card (OtherEdges f))) : Label :=
  crossLabel labels e f k a (edgeEnum f j)

def crossWeight (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e f : Fin r) (k a : Label) : ℂ :=
  weight a * MatchingCard.spliceScalar (labels a e) k (labels a f)

theorem crossWeight_ne_zero (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e f : Fin r) (k a : Label) : crossWeight weight labels e f k a ≠ 0 ↔ weight a ≠ 0 := by
  constructor
  · exact fun h => (mul_ne_zero_iff.mp h).1
  · exact fun h => mul_ne_zero h (MatchingCard.spliceScalar_ne_zero _ _ _)

theorem product_crossed (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (e f : Fin r) (hef : e ≠ f) (k a : Label) :
    productValue (splicePorts M.ports e f)
      (spliceFactors (MatchingCard.asMatrix (dual k))
        (fun j => MatchingCard.asMatrix (E (labels a j))) e f) (weight a) =
    fun x => crossWeight weight labels e f k a *
      (crossed M e f).tensor (crossLabels labels e f k a) x := by
  classical
  funext x
  let s := MatchingCard.spliceScalar (labels a e) k (labels a f)
  have hfactors (d : OtherEdges f) :
      spliceFactors (MatchingCard.asMatrix (dual k))
        (fun j => MatchingCard.asMatrix (E (labels a j))) e f d =
      (if d.val = e then s else 1) • MatchingCard.asMatrix (E (crossLabel labels e f k a d)) := by
    by_cases hd : d.val = e
    · simp only [spliceFactors,hd,ite_true,crossLabel]
      exact (MatchingCard.fuse_dual _ _ _).trans (MatchingCard.asMatrix_scale _ _)
    · simp only [spliceFactors,hd,ite_false,crossLabel,one_smul]
  have hprod : (∏ d : OtherEdges f, if d.val = e then s else 1) = s := by
    let e' : OtherEdges f := ⟨e,hef⟩
    have he (d : OtherEdges f) : d.val = e ↔ d = e' := by
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    simp_rw [he]
    simp
  simp only [productValue]
  simp_rw [hfactors]
  simp only [Matrix.smul_apply,smul_eq_mul,MatchingCard.asMatrix,Matrix.of_apply,
    Finset.prod_mul_distrib,hprod]
  change weight a * (s * _) = (weight a * s) * _
  rw [←mul_assoc]
  congr 1
  exact (edgeEnum f).prod_comp (fun d => E (crossLabel labels e f k a d)
    (x (splicePorts M.ports e f (d,false)))
    (x (splicePorts M.ports e f (d,true)))) |>.symm

theorem contract_fiber_cross (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (e f : Fin r) (hef : e ≠ f) (k : Label) :
    contractPair (M.ports (e,true)) (M.ports (f,false))
      (MatchingCard.asMatrix (dual k)) (Fiber.tensor M weight labels) =
    Fiber.tensor (crossed M e f) (crossWeight weight labels e f k)
      (crossLabels labels e f k) := by
  change contractPair _ _ _ (fun x => ∑ a, weight a * M.tensor (labels a) x) = _
  rw [contract_sum]
  funext x
  apply Finset.sum_congr rfl
  intro a ha
  have h := contract_cross M.ports
    (fun j => MatchingCard.asMatrix (E (labels a j))) (weight a) e f hef
    (MatchingCard.asMatrix (dual k))
  rw [product_crossed M weight labels e f hef k a] at h
  have he : productValue M.ports (fun j => MatchingCard.asMatrix (E (labels a j)))
      (weight a) = (fun y => weight a * M.tensor (labels a) y) := rfl
  rw [he] at h
  exact congrFun h x

/-- Cross two residual edges and keep the distinguished edge. Every original
nonzero coefficient remains nonzero, so the ACTUAL ancestor has0/1/4 live rows. -/
theorem live_count (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished e f : Fin r)
    (hde : distinguished ≠ e) (hdf : distinguished ≠ f) (hef : e ≠ f)
    (hlabel : ∀ a, labels a distinguished = a)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels)) :
    Fintype.card {a : Label // weight a ≠ 0} = 0 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 1 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 4 := by
  classical
  have huv : M.ports (e,true) ≠ M.ports (f,false) := by
    intro h
    exact hef (congrArg Prod.fst (M.ports.injective h))
  have hsafe := hs _ _ huv (0 : Label)
  rw [contract_fiber_cross M weight labels e f hef] at hsafe
  let j := (edgeEnum f).symm ⟨distinguished,hdf⟩
  have hj : ∀ a, crossLabels labels e f 0 a j = a := by
    intro a
    simp only [crossLabels,j,Equiv.apply_symm_apply,crossLabel,hde,ite_false,hlabel]
  have hc := Fiber.safe_support_card (crossed M e f) (crossWeight weight labels e f 0)
    (crossLabels labels e f 0) j hj hsafe
  have he : Fintype.card {a : Label // crossWeight weight labels e f 0 a ≠ 0} =
      Fintype.card {a : Label // weight a ≠ 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun a =>
      crossWeight_ne_zero weight labels e f 0 a))
  rwa [he] at hc

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
