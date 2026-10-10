import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparsePinTwist

/-! Uniform-twisted minimum-rank descent. The twist is used only for semantic
class testing. Every returned physical row remains a pure pinning of the
unchanged original coefficient-field signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseUniformMinimal
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSparseMinimalRank OrdinaryNegativeSparsePinTwist
open OrdinaryNegativeAffineRankOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n r : ℕ}

def supportChart {g h : Signature AlgebraicComplex n} (D : SystematicSupport g r)
    (support : ∀x,g x≠0 ↔ h x≠0) : SystematicSupport h r where
  ports := D.ports
  injective := D.injective
  encode := D.encode
  affine := D.affine
  free := D.free
  supported x := (support _).mp (D.supported x)
  covers x hx := D.covers x ((support x).mpr hx)

/-- The uniform semantic chart has exactly the same physical ports and
encoding as the original row. -/
def uniformChart {f : Signature AlgebraicComplex n} (D : SystematicSupport f r) :
    SystematicSupport (uniform f) r :=
  supportChart D (fun x=>(uniform_support f x).symm)

/-- Actual pinning of the semantic uniform row differs from uniform twist
of the original pin minor only by the explicit nonzero pinned phase scalar. -/
theorem uniform_minor_affine_iff {f : Signature AlgebraicComplex n}
    (D : SystematicSupport f r) (S : Finset (Fin r)) (z : Word r) :
    Affine (minor (uniformChart D) S z) ↔ Affine (uniform (minor D S z)) := by
  change Affine (literal (uniform f) (remaining D S) (D.encode z)) ↔
    Affine (uniform (literal f (remaining D S) (D.encode z)))
  rw [literal_substitution,literal_substitution]
  exact uniform_pin_affine_iff f _ (substitution_unique _ _)

variable {K : IntermediateField ℚ AlgebraicComplex}

structure UniformPinWitness (f : Signature K n) (rank : ℕ) where
  arity : ℕ
  pins : Fin n→Bool ⊕ Fin arity
  pure : PurePins pins
  chart : SystematicSupport (row f pins) rank
  bad : ¬Affine (uniform (row f pins))

/-- Low-rank selection on the twisted semantic row is transported back to
original coefficients using exact nonzero pin-scalar commutation. -/
theorem exists_low_rank (f : Signature K n)
    (square : Affine (fun x=>(f x : AlgebraicComplex)^2)) (nonzero : f≠0)
    (bad : ¬Affine (uniform (fun x=>(f x : AlgebraicComplex)))) :
    ∃rank : ℕ,1≤rank ∧ rank≤3 ∧ Nonempty (UniformPinWitness f rank) := by
  let F : Signature AlgebraicComplex n := fun x=>(f x : AlgebraicComplex)
  let twisted : Signature (⊤ : IntermediateField ℚ AlgebraicComplex) n :=
    fun x=>⟨uniform F x,by trivial⟩
  have hn : twisted≠0 := by
    obtain ⟨a,ha⟩ := Function.ne_iff.mp nonzero
    change f a≠0 at ha
    have hc : (f a : AlgebraicComplex)≠0 := fun hz=>ha (Subtype.ext hz)
    intro hz
    exact (uniform_support F a).mpr hc (congrArg Subtype.val (congrFun hz a))
  have hs : Affine (fun x=>(twisted x : AlgebraicComplex)^2) := uniform_square F square
  obtain ⟨m,k,p,lo,hi,pure,⟨chart⟩,hbad,hSq⟩ := exists_original_low_rank twisted hs hn bad
  let chartOriginal : SystematicSupport (row f p) k :=
    supportChart chart (fun x=>uniform_support F (T.substitute p x))
  have hb : ¬Affine (uniform (row f p)) := by
    intro h
    exact hbad ((uniform_pin_affine_iff F p pure).mpr h)
  exact ⟨k,lo,hi,⟨⟨m,p,pure,chartOriginal,hb⟩⟩⟩

namespace UniformPinWitness
variable {f : Signature K n} {rank : ℕ} (W : UniformPinWitness f rank)

theorem square (h : Affine (fun x=>(f x : AlgebraicComplex)^2)) :
    Affine (fun x=>row f W.pins x^2) := h.precompose _ (substitute_affine W.pins)

include W in
theorem rank_positive (h : Affine (fun x=>(f x : AlgebraicComplex)^2)) : 1≤rank := by
  let D := supportChart W.chart (fun x=>(uniform_support (row f W.pins) x).symm)
  have hn : uniform (row f W.pins)≠0 := by
    intro hz
    exact D.supported (origin rank) (congrFun hz _)
  exact OrdinaryNegativeSparseRankDescent.rank_positive D
    (uniform_square _ (W.square h)) hn W.bad

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

/-- Smaller uniform-class faces remain Affine under arbitrary affine
logical maps into those faces. The pinned original phase scalar is retained
and removed only using its proved nonzero value. -/
theorem affine_face_precompose {m : ℕ} (S : Finset (Fin rank)) (z : Word rank)
    (h : Affine (uniform (minor W.chart S z))) (q : Word m→Word rank)
    (hq : IsAffineMap q) (fixed : ∀x i,i∉S → q x i=z i) :
    Affine (fun x=>uniform (row f W.pins) (W.chart.encode (q x))) := by
  let U := remaining W.chart S
  let p := substitution U (W.chart.encode z)
  have he : (fun y=>row f W.pins (T.substitute p y))=minor W.chart S z :=
    (literal_substitution (row f W.pins) U (W.chart.encode z)).symm
  have hcut : Affine (literal (uniform (row f W.pins)) U (W.chart.encode z)) := by
    rw [literal_substitution]
    apply (uniform_pin_affine_iff (row f W.pins) p (substitution_unique _ _)).mpr
    rwa [he]
  have hmap : IsAffineMap (fun x=>project U (W.chart.encode (q x))) :=
    affine_map_comp (project U) (fun x=>W.chart.encode (q x)) (project_affine U)
      (affine_map_comp W.chart.encode q W.chart.affine hq)
  have ha := hcut.precompose _ hmap
  convert ha using 1
  funext x
  unfold literal
  rw [fill_remaining W.chart S z (q x) (fixed x)]

/-- Fixing even one information coordinate of a minimal uniform-class
witness makes every affine pullback of that face Affine. -/
theorem affine_of_fixed_coordinate
    (minimal : ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,
      Affine (uniform (minor W.chart S z))) {m : ℕ}
    (q : Word m→Word rank) (hq : IsAffineMap q) (j : Fin rank) (b : Bool)
    (fixed : ∀x,q x j=b) :
    Affine (fun x=>uniform (row f W.pins) (W.chart.encode (q x))) := by
  let S : Finset (Fin rank) := Finset.univ.erase j
  have smaller : S.card<rank := by
    simpa [S] using Finset.card_erase_lt_of_mem (Finset.mem_univ j)
  apply W.affine_face_precompose S (fun _=>b) (minimal S smaller (fun _=>b)) q hq
  intro x i hi
  have he : i=j := by simpa [S] using hi
  subst i
  exact fixed x

def smaller (S : Finset (Fin rank)) (z : Word rank)
    (bad : ¬Affine (uniform (minor W.chart S z))) : UniformPinWitness f S.card where
  arity := (remaining W.chart S).card
  pins := W.facePins S z
  pure := W.facePins_pure S z
  chart := by rw [W.facePins_value];exact minorChart W.chart S z
  bad := by rwa [W.facePins_value]

end UniformPinWitness

/-- The uniform-twisted alternative has the same internally selected,
original-field, proper-face-minimal rank-one/two/three normal form. -/
theorem exists_minimal_uniform (f : Signature K n)
    (square : Affine (fun x=>(f x : AlgebraicComplex)^2)) (nonzero : f≠0)
    (bad : ¬Affine (uniform (fun x=>(f x : AlgebraicComplex)))) :
    ∃rank : ℕ,1≤rank ∧ rank≤3 ∧ ∃W : UniformPinWitness f rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,
        Affine (uniform (minor W.chart S z)) := by
  classical
  obtain ⟨k,lo,hi,⟨initial⟩⟩ := exists_low_rank f square nonzero bad
  have existsRank : ∃j : ℕ,Nonempty (UniformPinWitness f j) := ⟨k,⟨initial⟩⟩
  let rank := Nat.find existsRank
  obtain ⟨W⟩ := Nat.find_spec existsRank
  have upper : rank≤3 := le_trans (Nat.find_min' existsRank ⟨initial⟩) hi
  refine ⟨rank,W.rank_positive square,upper,W,?_⟩
  intro S smaller z
  by_contra ha
  exact Nat.find_min existsRank smaller ⟨W.smaller S z ha⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseUniformMinimal
end
