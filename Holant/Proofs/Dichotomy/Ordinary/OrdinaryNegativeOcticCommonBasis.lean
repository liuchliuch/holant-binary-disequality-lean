import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticPhaseExtraction
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicExtraction
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinaryTerminal
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentSquareClass

/-! Whole-family compatibility in the low-order octic residue. One uniform
unary fourth-power parity gives one actual diagonal affine basis for every
row, Eq4, both pins, and the equality edge. Failure of the finite common-basis
criterion therefore produces two actual incompatible unary phase entries. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticCommonBasis
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.LocalDrafts.MainChain
open scoped BigOperators
namespace C
export OrdinaryNegativeOcticPhaseCore (lowOrder pair interaction)
end C
namespace E
export OrdinaryNegativeOcticPhaseExtraction (normalized normalized_eight)
end E
namespace N
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization
  (Edge unary affine_prod)
end N
namespace T
export StableHigherCurrentOrdinaryTerminal (Obstruction Test AffineTest obstruction_iff)
end T
open StableHigherCurrentAnchorCriterion (eq4)
abbrev pin := StableHigherCurrentAnchorLocalBasis.pin
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def parity (b : Bool) : AlgebraicComplex := if b then -1 else 1
def phase (b : Bool) : AlgebraicComplex := if b then zetaEight else 1

@[simp] theorem phase_ne (b : Bool) : phase b≠0 := by cases b <;> simp [phase,zetaEight_ne_zero]
@[simp] theorem phase_four (b : Bool) : phase b^4=parity b := by cases b <;> simp [phase,parity,zetaEight_pow_four]
@[simp] theorem phase_eight (b : Bool) : phase b^8=1 := by cases b <;> simp [phase,zetaEight_pow_eight]
@[simp] theorem parity_sq (b : Bool) : parity b^2=1 := by cases b <;> norm_num [parity]

/-- The inverse action multiplies every true coordinate by the same phase. -/
def basis (b : Bool) : InvertibleKernel where
  matrix := diagonalKernel 1 (phase b)⁻¹
  inverse := diagonalKernel 1 (phase b)
  matrix_inverse := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul,diagonalKernel,Signature.equality]
  inverse_matrix := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul,diagonalKernel,Signature.equality]

theorem action {n : ℕ} (b : Bool) (f : Signature AlgebraicComplex n) :
    (basis b).symm.action f=fun x=>(∏i,if x i then phase b else 1)*f x :=
  coordinateAction_diagonal 1 (phase b) f

theorem edge_affine (b : Bool) :
    Affine (kernelSignature (Kernel.pullback Signature.equality (basis b).matrix)) := by
  have h : Kernel.pullback Signature.equality (basis b).matrix=diagonal 1 ((phase b)⁻¹^2) := by
    funext x y
    cases x <;> cases y <;> simp [basis,Kernel.pullback,Kernel.mul,Kernel.transpose,
      diagonalKernel,diagonal,Signature.equality,pow_two]
  rw [h]
  apply affine_diagonal_of_fourth_power_eq 1 _ one_ne_zero
  rw [one_pow,←pow_mul,inv_pow,phase_eight]
  simp

theorem coordinate_affine {n : ℕ} (i : Fin n) (v : AlgebraicComplex) (hv : v^4=1) :
    Affine (fun x : Fin n→Bool=>if x i then v else 1) := by
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hv
  rw [←hq]
  exact StableHigherCurrentSquareClass.affine_coordinate_phase i q

theorem signed_pair_affine {n : ℕ} (i j : Fin n) (v : AlgebraicComplex) (hv : v^2=1) :
    Affine (fun x : Fin n→Bool=>if x i && x j then v else 1) := by
  have hb : Affine (fun z : Fin 2→Bool=>if z 0 && z 1 then v else 1) := by
    apply OrdinaryNegativeCubicExtraction.binary_square_affine
    intro z
    split_ifs <;> simp_all
  have hm : TwoTranslate.IsAffineMap (fun x : Fin n→Bool=>![x i,x j]) := by
    convert coordinates_isAffineMap (![i,j] : Fin 2→Fin n) using 1
    funext x k
    fin_cases k <;> rfl
  simpa using hb.precompose (fun x : Fin n→Bool=>![x i,x j]) hm

def LowOrder {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∀x,f x=f (AffinePhase.origin n)*C.lowOrder (E.normalized f) x
def SignedPairs {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∀e : N.Edge n,C.interaction (E.normalized f) e^2=1
def UnaryParity {n : ℕ} (b : Bool) (f : Signature AlgebraicComplex n) : Prop :=
  ∀i : Fin n,E.normalized f (AffinePhase.basis i)^4=parity b

/-- Every row uses the same selected parity, not a separately selected basis. -/
theorem row_affine {n : ℕ} (b : Bool) (f : Signature AlgebraicComplex n)
    (hl : LowOrder f) (hp : SignedPairs f) (hu : UnaryParity b f) :
    Affine ((basis b).symm.action f) := by
  let g := E.normalized f
  have hunary (i : Fin n) : Affine (fun x : Fin n→Bool=>if x i then phase b*g (AffinePhase.basis i) else 1) := by
    apply coordinate_affine
    rw [mul_pow,phase_four,hu]
    simpa only [pow_two] using parity_sq b
  have hpair (e : N.Edge n) : Affine (C.pair g e) :=
    signed_pair_affine e.val.1 e.val.2 (C.interaction g e) (hp e)
  have ha := ((N.affine_prod _ hunary).mul (N.affine_prod _ hpair)).scale (f (AffinePhase.origin n))
  convert ha using 1
  funext x
  rw [action]
  dsimp only
  rw [hl x]
  simp only [C.lowOrder,N.unary]
  have hprod : (∏i : Fin n,if x i then phase b*g (AffinePhase.basis i) else 1)=
      (∏i : Fin n,if x i then phase b else 1)*(∏i : Fin n,if x i then g (AffinePhase.basis i) else 1) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> simp
  rw [hprod]
  ring

theorem pin_affine (b : Bool) : Affine (pin b) := by
  let S : AffineSystem 1 := ⟨1,fun _ _=>1,fun _=>bitValue (ZMod 2) b⟩
  convert affine_indicator S using 1
  funext x
  cases b <;> cases h : x 0 <;>
    simp [S,AffineSystem.Holds,pin,StableHigherCurrentAnchorLocalBasis.pin,h]

theorem pin_action_affine (b v : Bool) : Affine ((basis b).symm.action (pin v)) := by
  have h : (basis b).symm.action (pin v)=fun x=>(if v then phase b else 1)*pin v x := by
    rw [action]
    funext x
    cases v <;> cases hx : x 0 <;> simp [pin,StableHigherCurrentAnchorLocalBasis.pin,hx]
  rw [h]
  exact (pin_affine v).scale _

theorem equality_four_affine : Affine eq4 := by
  have he : Affine (kernelSignature (diagonal 1 1)) := by
    apply affine_diagonal_of_fourth_power_eq 1 1 one_ne_zero rfl
  have hp (j : Fin 4) : Affine (fun x : Fin 4→Bool=>if x j=x 0 then (1 : AlgebraicComplex) else 0) := by
    have hm : TwoTranslate.IsAffineMap (fun x : Fin 4→Bool=>![x j,x 0]) := by
      convert coordinates_isAffineMap (![j,0] : Fin 2→Fin 4) using 1
      funext x k
      fin_cases k <;> rfl
    simpa [kernelSignature,diagonal] using he.precompose (fun x : Fin 4→Bool=>![x j,x 0]) hm
  convert N.affine_prod _ hp using 1
  funext x
  simp [eq4,Holant.EightVertex.ProductAnchor.equalityFour,Fintype.prod_boole]

theorem equality_four_action_affine (b : Bool) : Affine ((basis b).symm.action eq4) := by
  have ha := (coordinate_affine (0 : Fin 4) (phase b^4) (by
    rw [phase_four]
    calc
      parity b^4=(parity b^2)^2 := by ring
      _=1 := by rw [parity_sq]; norm_num)).mul equality_four_affine
  convert ha using 1
  funext x
  rw [action]
  dsimp only
  by_cases h : ∀i : Fin 4,x i=x 0
  · have hp : (∏i : Fin 4,if x i then phase b else 1)=(if x 0 then phase b^4 else 1) := by
      simp_rw [h]
      cases x 0 <;> simp
    rw [hp]
  · simp [eq4,Holant.EightVertex.ProductAnchor.equalityFour,h]

def anchored (F : SignatureFamily AlgebraicComplex) : SignatureFamily AlgebraicComplex :=
  ((F∪{⟨4,eq4⟩})∪{⟨1,pin false⟩})∪{⟨1,pin true⟩}

theorem common_basis {F : SignatureFamily AlgebraicComplex} (b : Bool)
    (hL : ∀f∈F,LowOrder f.2) (hP : ∀f∈F,SignedPairs f.2)
    (hU : ∀f∈F,UnaryParity b f.2) : IsCommonBasis affineClass (anchored F) (basis b) := by
  refine ⟨edge_affine b,?_⟩
  intro f hf
  rcases hf with ((hf|rfl)|rfl)|rfl
  · exact row_affine b f.2 (hL f hf) (hP f hf) (hU f hf)
  · exact equality_four_action_affine b
  · exact pin_action_affine b false
  · exact pin_action_affine b true

theorem test_of_uniform {F : SignatureFamily AlgebraicComplex} (finite : F.Finite) (b : Bool)
    (hL : ∀f∈F,LowOrder f.2) (hP : ∀f∈F,SignedPairs f.2)
    (hU : ∀f∈F,UnaryParity b f.2) : T.Test (anchored F) := by
  apply Or.inl
  have hfin : (anchored F).Finite :=
    (((finite.union (Set.finite_singleton _)).union (Set.finite_singleton _)).union (Set.finite_singleton _))
  have hc : CommonTransformable affineClass (anchored F) := ⟨hfin,basis b,common_basis b hL hP hU⟩
  exact (StableHigherCurrentAnchorAffineBasisCandidates.common_transformable_iff_candidates
    (H:=anchored F) (Or.inl (Or.inr rfl)) (Or.inr rfl) (Or.inl (Or.inl (Or.inr rfl)))).mp hc |>.2

/-- A rejected common family internally supplies two different actual unary
fourth powers in the regular low-order residue. No conflict witness is input. -/
theorem obstruction_unary_conflict {F : SignatureFamily AlgebraicComplex} (finite : F.Finite)
    (hL : ∀f∈F,LowOrder f.2) (hP : ∀f∈F,SignedPairs f.2)
    (h8 : ∀f∈F,∀i : Fin f.1,E.normalized f.2 (AffinePhase.basis i)^8=1)
    (obstruction : T.Obstruction (anchored F)) :
    ∃f∈F,∃g∈F,∃i : Fin f.1,∃j : Fin g.1,
      E.normalized f.2 (AffinePhase.basis i)^4≠E.normalized g.2 (AffinePhase.basis j)^4 := by
  by_contra h
  push Not at h
  apply (T.obstruction_iff _).mp obstruction
  by_cases hp : ∃f∈F,∃i : Fin f.1,E.normalized f.2 (AffinePhase.basis i)^4=1
  · obtain ⟨f,hf,i,hi⟩ := hp
    apply test_of_uniform finite false hL hP
    intro g hg j
    exact (h g hg f hf j i).trans hi
  · apply test_of_uniform finite true hL hP
    intro f hf i
    have hn : E.normalized f.2 (AffinePhase.basis i)^4≠1 := fun he=>hp ⟨f,hf,i,he⟩
    have he : (E.normalized f.2 (AffinePhase.basis i)^4)^2=1 := by
      rw [←pow_mul]
      exact h8 f hf i
    exact (sq_eq_one_iff.mp he).resolve_left hn

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticCommonBasis
end
