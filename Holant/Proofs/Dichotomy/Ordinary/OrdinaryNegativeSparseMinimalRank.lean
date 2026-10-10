import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankDescent
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineCharacters

/-! Minimal rank is selected internally among genuine pinning minors of the
unchanged original row. Every further proper logical coordinate face is
proved Affine, with its actual original-port substitution retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMinimalRank
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace I
def compose {n m l : ℕ} (p : Fin n→Bool ⊕ Fin m) (q : Fin m→Bool ⊕ Fin l) :
    Fin n→Bool ⊕ Fin l:=fun i=>Sum.elim Sum.inl q (p i)
theorem substitute_compose {n m l : ℕ} (p : Fin n→Bool ⊕ Fin m)
    (q : Fin m→Bool ⊕ Fin l) (z : Fin l→Bool) :
    T.substitute (compose p q) z=T.substitute p (T.substitute q z) := by
  funext i
  cases h:p i <;> simp [compose,T.substitute,h]
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m l : ℕ}

def PurePins (p : Fin n→Bool ⊕ Fin m) : Prop := ∀i,∃!j,p j=Sum.inr i

theorem pure_compose (p : Fin n→Bool ⊕ Fin m) (q : Fin m→Bool ⊕ Fin l)
    (hp : PurePins p) (hq : PurePins q) : PurePins (I.compose p q) := by
  intro i
  obtain ⟨k,hk,uniqueK⟩ := hq i
  obtain ⟨j,hj,uniqueJ⟩ := hp k
  refine ⟨j,by simp [I.compose,hj,hk],?_⟩
  intro a ha
  cases he : p a with
  | inl b => simp [I.compose,he] at ha
  | inr t =>
    have ht : q t=Sum.inr i := by simpa [I.compose,he] using ha
    have htk : t=k := uniqueK t ht
    exact uniqueJ a (by simpa [htk] using he)

theorem substitute_affine (p : Fin n→Bool ⊕ Fin m) : IsAffineMap (T.substitute p) := by
  intro x y
  funext j
  cases h : p j with
  | inl b => cases b <;> simp [T.substitute,h,AffinePhase.xor]
  | inr i => simp [T.substitute,h,AffinePhase.xor,origin]

variable {K : IntermediateField ℚ AlgebraicComplex}

def row (f : Signature K n) (p : Fin n→Bool ⊕ Fin m) : Signature AlgebraicComplex m :=
  fun x=>(f (T.substitute p x) : AlgebraicComplex)

/-- The bad row is an actual original pure pinning with unchanged coefficient
values and a proved systematic physical support chart. -/
structure PinWitness (f : Signature K n) (rank : ℕ) where
  arity : ℕ
  pins : Fin n→Bool ⊕ Fin arity
  pure : PurePins pins
  chart : SystematicSupport (row f pins) rank
  bad : ¬Affine (row f pins)

namespace PinWitness
variable {f : Signature K n} {rank : ℕ} (W : PinWitness f rank)

theorem square (h : Affine (fun x=>(f x : AlgebraicComplex)^2)) :
    Affine (fun x=>row f W.pins x^2) := h.precompose _ (substitute_affine W.pins)

theorem nonzero : row f W.pins≠0 := by
  intro hz
  exact W.chart.supported (origin rank) (congrFun hz _)

def facePins (S : Finset (Fin rank)) (z : Word rank) :
    Fin n→Bool ⊕ Fin (remaining W.chart S).card :=
  I.compose W.pins (substitution (remaining W.chart S) (W.chart.encode z))

theorem facePins_pure (S : Finset (Fin rank)) (z : Word rank) : PurePins (W.facePins S z) :=
  pure_compose _ _ W.pure (substitution_unique _ _)

theorem facePins_value (S : Finset (Fin rank)) (z : Word rank) :
    row f (W.facePins S z)=minor W.chart S z := by
  funext x
  simp only [row,facePins,I.substitute_compose]
  exact (congrFun (literal_substitution (row f W.pins)
    (remaining W.chart S) (W.chart.encode z)) x).symm

/-- Smaller-face affinity also gives the exact compressed phase test,
without asserting that the compressed row is a physical gate. -/
theorem logical_face_affine (S : Finset (Fin rank)) (z : Word rank)
    (h : Affine (minor W.chart S z)) : Affine (literal W.chart.reduced S z) := by
  have hc := (minorChart W.chart S z).reduced_affine h
  rwa [minorChart_reduced] at hc

/-- A proper face remains Affine after any affine Boolean substitution,
including arbitrary repeated linear characters in its unpinned coordinates. -/
theorem affine_face_precompose {m : ℕ} (S : Finset (Fin rank)) (z : Word rank)
    (h : Affine (minor W.chart S z)) (q : Word m→Word rank)
    (hq : IsAffineMap q) (fixed : ∀x i,i∉S → q x i=z i) :
    Affine (fun x=>row f W.pins (W.chart.encode (q x))) := by
  have ha := (face_affine_of_minor W.chart S z h).precompose q hq
  convert ha using 1
  funext x
  exact (ite_eq_left (fixed x)).symm

/-- The minimal-rank hypothesis proves every affine coordinate map with at
least one fixed information coordinate has an Affine compressed value row. -/
theorem affine_of_fixed_coordinate
    (minimal : ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,
      Affine (minor W.chart S z)) {m : ℕ}
    (q : Word m→Word rank) (hq : IsAffineMap q) (j : Fin rank) (b : Bool)
    (fixed : ∀x,q x j=b) : Affine (fun x=>row f W.pins (W.chart.encode (q x))) := by
  let S : Finset (Fin rank) := Finset.univ.erase j
  have smaller : S.card<rank := by
    simpa [S] using Finset.card_erase_lt_of_mem (Finset.mem_univ j)
  apply W.affine_face_precompose S (fun _=>b) (minimal S smaller (fun _=>b)) q hq
  intro x i hi
  have he : i=j := by simpa [S] using hi
  subst i
  exact fixed x

/-- Further logical pinning is composed into the original row itself. -/
def smaller (S : Finset (Fin rank)) (z : Word rank)
    (bad : ¬Affine (minor W.chart S z)) : PinWitness f S.card where
  arity := (remaining W.chart S).card
  pins := W.facePins S z
  pure := W.facePins_pure S z
  chart := by rw [W.facePins_value];exact minorChart W.chart S z
  bad := by rwa [W.facePins_value]

end PinWitness

/-- Minimum rank is not a caller premise: it is chosen among actual original
pin minors. Every strictly smaller logical face, at every outside assignment,
is Affine. The rank remains between one and three. -/
theorem exists_minimal (f : Signature K n)
    (square : Affine (fun x=>(f x : AlgebraicComplex)^2)) (nonzero : f≠0)
    (bad : ¬Affine (fun x=>(f x : AlgebraicComplex))) :
    ∃rank : ℕ,1≤rank ∧ rank≤3 ∧ ∃W : PinWitness f rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,Affine (minor W.chart S z) := by
  classical
  obtain ⟨m,k,p,lo,hi,pure,⟨chart⟩,bad,hSq⟩ := exists_original_low_rank f square nonzero bad
  let initial : PinWitness f k := ⟨m,p,pure,chart,bad⟩
  have existsRank : ∃j : ℕ,Nonempty (PinWitness f j) := ⟨k,⟨initial⟩⟩
  let rank := Nat.find existsRank
  obtain ⟨W⟩ := Nat.find_spec existsRank
  have upper : rank≤3 := le_trans (Nat.find_min' existsRank ⟨initial⟩) hi
  have lower : 1≤rank := rank_positive W.chart (W.square square) W.nonzero W.bad
  refine ⟨rank,lower,upper,W,?_⟩
  intro S smaller z
  by_contra ha
  exact Nat.find_min existsRank smaller ⟨W.smaller S z ha⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMinimalRank
end
