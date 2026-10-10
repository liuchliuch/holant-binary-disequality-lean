import Holant.Proofs.Hardness.GeneralEOPureAffineSpan
import Holant.Proofs.Hardness.GeneralEODEQProducerStep
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionTensor

/-! Literal deletion of a forced oriented pair. The class operations here are
semantic reconstruction identities; no pin signature is added to the palette. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureLoopCore
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n m s : ℕ} {a : ℕ → ℕ}

structure Reduced (G : (i : Fin s) → Signature AlgebraicComplex (a i.val)) (C : EOClass) where
  arity : ℕ
  network : Network AlgebraicComplex arity
  labels : Labelling network.shape s 1 a
  exact : LabelledNetwork.Exact G network labels
  native : ∀ e, network.edge e = Signature.disequality
  central : Signature.CentralSupport network.denote
  nonzero : network.denote ≠ 0
  closed : GeneralEONegativeClosedSupport.Closed network.denote
  pairing : OrientedPerfectPairing arity
  bad : ¬C.Holds (pairing.restrict network.denote)

theorem Reduced.failure {G : (i : Fin s) → Signature AlgebraicComplex (a i.val)}
    {C : EOClass} (R : Reduced G C) :
    ¬EONegativeWitness.Pairings C ⟨R.arity,R.network.denote⟩ := fun h => R.bad (h R.pairing)

theorem class_zero (C : EOClass) : C.Holds (0 : Signature AlgebraicComplex n) := by
  cases C <;> simp [EOClass.Holds]

theorem nonzero_of_bad (f : Signature AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (C : EOClass) (h : ¬C.Holds (p.restrict f)) : f ≠ 0 := by
  rintro rfl
  exact h (class_zero C)

theorem class_coordinates (C : EOClass) (indices : Fin n → Fin m)
    (f : Signature AlgebraicComplex n) (hf : C.Holds f) :
    C.Holds (fun x => f (x ∘ indices)) := by
  cases C with
  | affine => exact Affine.precompose hf _ (coordinates_isAffineMap indices)
  | product =>
    exact GeneralEOPairedFamilyExtractionTensor.product_substitute (fun j => Sum.inr (indices j)) hf

def pinSystem (j : Fin n) (b : Bool) : AffineSystem n where
  rows := 1
  matrix _ k := if k = j then 1 else 0
  rhs _ := bitValue (ZMod 2) b

theorem pinSystem_holds (j : Fin n) (b : Bool) (x : Fin n → Bool) :
    (pinSystem j b).Holds x ↔ x j = b := by
  simp only [AffineSystem.Holds, pinSystem]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [forall_const]
  cases x j <;> cases b <;> norm_num [bitValue]

theorem class_pin (C : EOClass) (j : Fin n) (b : Bool) :
    C.Holds (fun x => if x j = b then 1 else 0 : Signature AlgebraicComplex n) := by
  cases C with
  | affine => simpa only [pinSystem_holds, EOClass.Holds] using affine_indicator (pinSystem j b)
  | product => exact product_unary j (fun z => if z = b then 1 else 0)

theorem class_mul (C : EOClass) (f g : Signature AlgebraicComplex n)
    (hf : C.Holds f) (hg : C.Holds g) : C.Holds (fun x => f x * g x) := by
  cases C with
  | affine => exact Affine.mul hf hg
  | product => exact Product.mul hf hg

/-- A fixed compressed coordinate is recovered by an actual unary indicator. -/
theorem class_recover (C : EOClass) (f : Signature AlgebraicComplex n)
    (g : Signature AlgebraicComplex m) (indices : Fin m → Fin n) (j : Fin n) (b : Bool)
    (he : ∀ x, f x = (if x j = b then 1 else 0) * g (x ∘ indices))
    (hg : C.Holds g) : C.Holds f := by
  have hh := class_mul C _ _ (class_pin C j b) (class_coordinates C indices g hg)
  convert hh using 1
  funext x
  exact he x

/-- Row-major, original-order standard pairing. -/
def standard (m : ℕ) : OrientedPerfectPairing (m*2) where
  count := m
  ports := (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

def expanded (m : ℕ) : OrientedPerfectPairing (m*2+2) where
  count := m+1
  ports := (standard (m+1)).ports.trans (finCongr (by omega))

@[simp] theorem expanded_false : (expanded m).ports ((0 : Fin (m+1)),false) = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem expanded_true : (expanded m).ports ((0 : Fin (m+1)),true) = 1 := by
  apply Fin.ext
  rfl

@[simp] theorem expanded_succ (i : Fin m) (b : Bool) :
    (expanded m).ports (i.succ,b) = ((standard m).ports (i,b)).succ.succ := by
  apply Fin.ext
  change (finTwoEquiv.symm b).val + 2 * (i.val + 1) =
    ((finTwoEquiv.symm b).val + 2 * i.val) + 1 + 1
  omega

theorem expanded_word (z : Fin (m+1) → Bool) :
    (expanded m).word z = GeneralEOPinnedDescentOperations.word (z 0) (!(z 0))
      ((standard m).word (fun i => z i.succ)) := by
  funext k
  obtain ⟨⟨i,b⟩,rfl⟩ := (expanded m).ports.surjective k
  simp only [OrientedPerfectPairing.word,Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · cases b <;> simp [GeneralEOPinnedDescentOperations.word]
  · rw [expanded_succ]
    simp [GeneralEOPinnedDescentOperations.word,OrientedPerfectPairing.word]

/-- Normalize all pairs, bringing the chosen compressed coordinate first. -/
def normalize (p : OrientedPerfectPairing n) (e : Fin (m+1) ≃ Fin p.count) :
    Fin (m*2+2) ≃ Fin n :=
  (expanded m).ports.symm.trans ((Equiv.prodCongr e (Equiv.refl Bool)).trans p.ports)

@[simp] theorem normalize_port (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (i : Fin (m+1)) (b : Bool) :
    normalize p e ((expanded m).ports (i,b)) = p.ports (e i,b) := by
  simp only [normalize,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem word_normalize (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (z : Fin p.count → Bool) :
    p.word z ∘ normalize p e = (expanded m).word (z ∘ e) := by
  funext k
  obtain ⟨⟨i,b⟩,rfl⟩ := (expanded m).ports.surjective k
  simp [OrientedPerfectPairing.word]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureLoopCore
