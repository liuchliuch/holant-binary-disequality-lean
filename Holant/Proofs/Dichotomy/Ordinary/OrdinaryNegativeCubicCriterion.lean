import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCore
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinaryTerminal
import Holant.Tractable.AffinePhaseCriterion
import Holant.EightVertex.ProductAnchor.TemplateTransport

/-! A concrete negative phase slice. The cubic sign has an affine square but
is outside the literal affine and product classes. Seven Fibonacci unary
directions exclude every common affine basis without a candidate search;
full support excludes every common local-affine basis with both pins.
Together with the Eq4 Product rigidity, this proves the actual ordinary
terminal obstruction for any family containing the cubic, Eq4, and pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicCriterion
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.EightVertex.ProductAnchor
open OrdinaryNegativeCubicCore
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

@[simp] theorem cubic_square {K : Type*} [Ring K] (x : Fin 3 → Bool) :
    (cubic (K := K) x)^2 = 1 := by
  simp only [cubic]
  split <;> simp

@[simp] theorem cubic_ne_zero (x : Fin 3 → Bool) :
    cubic (K := AlgebraicComplex) x ≠ 0 := by
  simp only [cubic]
  split <;> norm_num

theorem cubic_square_affine : Affine (fun x => (cubic (K := AlgebraicComplex) x)^2) := by
  simpa only [cubic_square] using affine_constant 3 (1 : AlgebraicComplex)

theorem cubic_not_affine : ¬Affine (cubic (K := AlgebraicComplex)) := by
  intro h
  have ht := AffinePhase.thirdTrivial_of_affine cubic_ne_zero h
    (fun _ => false) ![true,false,false] ![false,true,false] ![false,false,true]
  norm_num [AffinePhase.thirdRatio,AffinePhase.xor,cubic] at ht

/-- The first-two-coordinate minor of every ternary face. -/
def FaceRankOne (f : Signature AlgebraicComplex 3) : Prop := ∀ b : Bool,
  f ![false,false,b] * f ![true,true,b] =
    f ![false,true,b] * f ![true,false,b]

theorem faceRankOne_mul {f g : Signature AlgebraicComplex 3}
    (hf : FaceRankOne f) (hg : FaceRankOne g) :
    FaceRankOne (fun x => f x * g x) := by
  intro b
  calc
    _ = (f ![false,false,b] * f ![true,true,b]) *
        (g ![false,false,b] * g ![true,true,b]) := by ring
    _ = _ := by rw [hf b,hg b]; ring

/-- Full support removes every genuine binary constraint in a Product list. -/
theorem product_full_support_face {f : Signature AlgebraicComplex 3}
    (hf : Product f) (hs : ∀ x, f x ≠ 0) : FaceRankOne f := by
  rcases hf with hz | ⟨a,ha,ps,rfl⟩
  · exact False.elim (hs (fun _ => false) (by simp [hz]))
  have hfactor (p : ProductFactor 3) (hp : p ∈ ps) : FaceRankOne p.eval := by
    cases p with
    | unary i vals hvals =>
        intro b
        fin_cases i <;> simp [ProductFactor.eval,mul_comm]
    | equality i j =>
        by_cases hij : i=j
        · subst j
          intro b
          simp [ProductFactor.eval,Signature.equality]
        · have hn := factor_nonzero_of_formula_nonzero a ps
            (fun k => decide (k=i)) (hs _) (.equality i j) hp
          exact False.elim (hn (by simp [ProductFactor.eval,Signature.equality,Ne.symm hij]))
    | disequality i j =>
        have hn := factor_nonzero_of_formula_nonzero a ps
          (fun _ => false) (hs _) (.disequality i j) hp
        exact False.elim (hn (by simp [ProductFactor.eval,Signature.disequality]))
  clear hs ha
  have H : FaceRankOne (fun x => (ps.map (fun p => p.eval x)).prod) := by
    induction ps with
    | nil => intro b; simp
    | cons p ps ih =>
        have hp := hfactor p (by simp)
        have hps := ih (fun q hq => hfactor q (by simp [hq]))
        simpa only [List.map_cons,List.prod_cons] using faceRankOne_mul hp hps
  exact faceRankOne_mul (f := fun _ => a) (by intro b; rfl) H

theorem cubic_not_product : ¬Product (cubic (K := AlgebraicComplex)) := by
  intro h
  have ht := product_full_support_face h cubic_ne_zero true
  norm_num [cubic] at ht

theorem cubic_not_localAffine : ¬LocalAffine (cubic (K := AlgebraicComplex)) := by
  intro h
  apply cubic_not_affine
  simpa using h (fun _ => false) (cubic_ne_zero _)

/-- For ternary full support, the origin twist and a one-bit twist already
contradict the fourth-power invariant of affine signatures. -/
theorem full_support_not_localAffine {f : Signature AlgebraicComplex 3}
    (hf : ∀ x, f x ≠ 0) : ¬LocalAffine f := by
  intro h
  have a0 := h (fun _ => false) (hf _)
  rw [localTwist_false] at a0
  have a1 := h ![true,false,false] (hf _)
  have p0 := a0.fourth_power_eq ![false,false,false] ![true,false,false] (hf _) (hf _)
  have p1 := a1.fourth_power_eq ![false,false,false] ![true,false,false]
    (by simpa [localTwist_apply,Fin.prod_univ_succ] using hf ![false,false,false])
    (by simpa [localTwist_apply,Fin.prod_univ_succ] using
      mul_ne_zero zetaEight_ne_zero (hf ![true,false,false]))
  have hp1 : f ![false,false,false]^4 = -f ![true,false,false]^4 := by
    simpa [localTwist_apply,Fin.prod_univ_succ,mul_pow] using p1
  have hz : f ![true,false,false]^4=0 := by linear_combination (hp1-p0)/2
  exact pow_ne_zero 4 (hf _) hz

/-- Monomial invertible tensor actions preserve full support. -/
theorem monomial_action_full_support (T : InvertibleKernel)
    (hT : Holant.EightVertex.ProductAnchor.Monomial T.matrix)
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : ∀ x, f x ≠ 0) :
    ∀ x, T.action f x ≠ 0 := by
  have hd := determinant_ne_zero T
  change ∀ x, Signature.coordinateAction (fun _ => T.matrix) f x ≠ 0
  rcases hT with ⟨h01,h10⟩ | ⟨h00,h11⟩
  · have hn : T.matrix false false≠0 ∧ T.matrix true true≠0 := by
      apply mul_ne_zero_iff.mp
      simpa [determinant,h01,h10] using hd
    have he : T.matrix=diagonalKernel (T.matrix false false) (T.matrix true true) := by
      funext a b
      cases a <;> cases b <;> simp [diagonalKernel,h01,h10]
    rw [he,coordinateAction_diagonal]
    intro x
    apply mul_ne_zero _ (hf x)
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    cases x i <;> simp [hn]
  · have hn : T.matrix false true≠0 ∧ T.matrix true false≠0 := by
      apply mul_ne_zero_iff.mp
      intro hz
      exact hd (by simp [determinant,h00,h11,hz])
    have he : T.matrix=Kernel.mul
        (diagonalKernel (T.matrix false true) (T.matrix true false)) Signature.disequality := by
      funext a b
      cases a <;> cases b <;>
        simp [Kernel.mul_apply,diagonalKernel,Signature.disequality,h00,h11]
    rw [he,coordinateAction_antidiagonal]
    intro x
    apply mul_ne_zero _ (hf _)
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    cases x i <;> simp [hn]

theorem no_common_product {H : SignatureFamily AlgebraicComplex}
    (heq : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) :
    ¬CommonTransformable productClass H := by
  intro h
  have hl := (StableHigherCurrentAnchorProductFamily.common_product_iff_literal heq).mp h
  exact cubic_not_product (hl.2 hc)

theorem no_common_localAffine {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin false⟩ : AnySignature AlgebraicComplex) ∈ H)
    (h1 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin true⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) :
    ¬CommonTransformable localAffineClass H := by
  rintro ⟨_,B,hB⟩
  have hm := (StableHigherCurrentAnchorLocalBasis.common_basis_monomial B h0 h1 hB).2
  exact full_support_not_localAffine (monomial_action_full_support B.symm hm cubic_ne_zero)
    (hB.2 _ hc)

/-- Semantic affine closure in the one fixed ordinary basis. -/
def InAffineBasis (B : InvertibleKernel) {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  Affine (B.symm.action f)

theorem affine_tensor {m n : ℕ} {f : Signature AlgebraicComplex m}
    {g : Signature AlgebraicComplex n} (hf : Affine f) (hg : Affine g) :
    Affine (Signature.tensor f g) := by
  exact (hf.precompose (fun x i => x (Fin.castAdd n i))
    (coordinates_isAffineMap (Fin.castAdd n))).mul
      (hg.precompose (fun x i => x (Fin.natAdd m i))
        (coordinates_isAffineMap (Fin.natAdd m)))

theorem InAffineBasis.tensor {B : InvertibleKernel} {m n : ℕ}
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n}
    (hf : InAffineBasis B f) (hg : InAffineBasis B g) :
    InAffineBasis B (Signature.tensor f g) := by
  unfold InAffineBasis InvertibleKernel.action at *
  rw [coordinateAction_tensor]
  exact affine_tensor hf hg

theorem InAffineBasis.reindex {B : InvertibleKernel} {n : ℕ}
    {f : Signature AlgebraicComplex n} (hf : InAffineBasis B f)
    (e : Equiv.Perm (Fin n)) : InAffineBasis B (Tensor.reindex e f) := by
  unfold InAffineBasis InvertibleKernel.action at *
  rw [ReedMuller.CoefficientAtlas.coordinateAction_reindex]
  exact hf.precompose (fun x i => x (e i)) (coordinates_isAffineMap e)

theorem InAffineBasis.contract {B : InvertibleKernel} {n : ℕ}
    {f : Signature AlgebraicComplex (n+2)} (hf : InAffineBasis B f)
    (hE : Affine (kernelSignature (Kernel.pullback Signature.equality B.matrix))) :
    InAffineBasis B (Signature.contract Signature.equality f) := by
  have he : Kernel.pullback (Kernel.pullback Signature.equality B.matrix) B.inverse =
      Signature.equality := by
    rw [←Holant.Tractable.pullback_mul,B.matrix_inverse]
    simp [Kernel.pullback]
  have h := Affine.contract hf (Kernel.pullback Signature.equality B.matrix) hE
  unfold InAffineBasis InvertibleKernel.action at *
  rw [ReedMuller.CoefficientAtlas.coordinateAction_contract] at h
  simpa only [InvertibleKernel.symm,he] using h

theorem InAffineBasis.scale {B : InvertibleKernel} {n : ℕ}
    {f : Signature AlgebraicComplex n} (hf : InAffineBasis B f) (c : AlgebraicComplex) :
    InAffineBasis B (fun x => c*f x) := by
  unfold InAffineBasis InvertibleKernel.action at *
  convert hf.scale c using 1
  funext x
  simp [Signature.coordinateAction,Finset.mul_sum,mul_left_comm]

/-- Two actual equality contractions attach unary rows to the first two ports. -/
def plugOrder : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (![0,2,4,1,3] : Fin 5 → Fin 5) (by decide)

def plug (f : Signature AlgebraicComplex 3) (u v : Signature AlgebraicComplex 1) :
    Signature AlgebraicComplex 1 :=
  Signature.contract Signature.equality (Signature.contract Signature.equality
    (Tensor.reindex plugOrder (Signature.tensor (Signature.tensor f u) v)))

theorem plug_apply (f : Signature AlgebraicComplex 3)
    (u v : Signature AlgebraicComplex 1) (x : Fin 1 → Bool) :
    plug f u v x =
      f ![false,false,x 0]*u ![false]*v ![false] +
      f ![true,false,x 0]*u ![true]*v ![false] +
      (f ![false,true,x 0]*u ![false]*v ![true] +
      f ![true,true,x 0]*u ![true]*v ![true]) := by
  have hf (a b : Bool) : (fun i : Fin 3 =>
      (Fin.cons a (Fin.cons a (Fin.cons b (Fin.cons b x))) : Fin 5 → Bool)
        (plugOrder (Fin.castAdd 1 (Fin.castAdd 1 i)))) = ![a,b,x 0] := by
    funext i
    fin_cases i <;> rfl
  have hu (a b : Bool) : (fun i : Fin 1 =>
      (Fin.cons a (Fin.cons a (Fin.cons b (Fin.cons b x))) : Fin 5 → Bool)
        (plugOrder (Fin.castAdd 1 (Fin.natAdd 3 i)))) = ![a] := by
    funext i
    fin_cases i; rfl
  have hv (a b : Bool) : (fun i : Fin 1 =>
      (Fin.cons a (Fin.cons a (Fin.cons b (Fin.cons b x))) : Fin 5 → Bool)
        (plugOrder (Fin.natAdd (3+1) i))) = ![b] := by
    funext i
    fin_cases i; rfl
  simp only [plug,Signature.contract_equality,Tensor.reindex,Signature.tensor_apply,hf,hu,hv]

theorem InAffineBasis.plug {B : InvertibleKernel}
    {f : Signature AlgebraicComplex 3} {u v : Signature AlgebraicComplex 1}
    (hf : InAffineBasis B f) (hu : InAffineBasis B u) (hv : InAffineBasis B v)
    (hE : Affine (kernelSignature (Kernel.pullback Signature.equality B.matrix))) :
    InAffineBasis B (plug f u v) :=
  ((((hf.tensor hu).tensor hv).reindex plugOrder).contract hE).contract hE

/-- A cubic sign capped twice with the zero pin supplies the constant unary. -/
theorem inBasis_ones {B : InvertibleKernel}
    (hc : InAffineBasis B (cubic (K := AlgebraicComplex)))
    (h0 : InAffineBasis B (StableHigherCurrentAnchorLocalBasis.pin false))
    (hE : Affine (kernelSignature (Kernel.pullback Signature.equality B.matrix))) :
    InAffineBasis B (fun _ : Fin 1 → Bool => 1) := by
  convert hc.plug h0 h0 hE using 1
  funext x
  simp [plug_apply,cubic,StableHigherCurrentAnchorLocalBasis.pin]

/-- Attaching a constant unary gives the Fibonacci map on the other unary,
with the exact scalar two removed through legitimate class scaling. -/
def advance (u : Signature AlgebraicComplex 1) : Signature AlgebraicComplex 1 :=
  fun x => if x 0 then u ![false] else u ![false]+u ![true]

theorem inBasis_advance {B : InvertibleKernel}
    (hc : InAffineBasis B (cubic (K := AlgebraicComplex)))
    (hone : InAffineBasis B (fun _ : Fin 1 → Bool => 1))
    (hE : Affine (kernelSignature (Kernel.pullback Signature.equality B.matrix)))
    {u : Signature AlgebraicComplex 1} (hu : InAffineBasis B u) :
    InAffineBasis B (advance u) := by
  convert (hc.plug hu hone hE).scale (1/2) using 1
  funext x
  rw [plug_apply]
  cases hx : x 0 <;> simp [advance,cubic,hx] <;> ring

/-- Seven distinct rational unary directions produced by the same phase row. -/
def fibonacciUnary : ℕ → Signature AlgebraicComplex 1
  | 0 => StableHigherCurrentAnchorLocalBasis.pin false
  | k+1 => advance (fibonacciUnary k)

theorem fibonacciUnary_inBasis {B : InvertibleKernel}
    (hc : InAffineBasis B (cubic (K := AlgebraicComplex)))
    (h0 : InAffineBasis B (StableHigherCurrentAnchorLocalBasis.pin false))
    (hE : Affine (kernelSignature (Kernel.pullback Signature.equality B.matrix)))
    (k : ℕ) : InAffineBasis B (fibonacciUnary k) := by
  induction k with
  | zero => exact h0
  | succ k ih => exact inBasis_advance hc (inBasis_ones hc h0 hE) hE ih

theorem fibonacciUnary_first_nonzero (i : Fin 7) : fibonacciUnary i.val ![false] ≠ 0 := by
  fin_cases i <;> norm_num [fibonacciUnary,advance,StableHigherCurrentAnchorLocalBasis.pin]

theorem fibonacciUnary_independent (i j : Fin 7) (hij : i ≠ j) :
    fibonacciUnary i.val ![false]*fibonacciUnary j.val ![true] -
      fibonacciUnary j.val ![false]*fibonacciUnary i.val ![true] ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [fibonacciUnary,advance,StableHigherCurrentAnchorLocalBasis.pin] at *

theorem unary_action_apply (T : InvertibleKernel) (u : Signature AlgebraicComplex 1)
    (b : Bool) : T.action u ![b] =
      T.matrix b false*u ![false]+T.matrix b true*u ![true] := by
  unfold InvertibleKernel.action Signature.coordinateAction
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  have hw (c : Bool) : (uniqueElim c : Fin 1 → Bool) = ![c] := by
    funext j
    fin_cases j; rfl
  simp only [Fin.prod_univ_one,Equiv.funUnique_symm_apply,Fintype.sum_bool,hw,Matrix.cons_val_zero]
  exact add_comm _ _

theorem unary_action_minor (T : InvertibleKernel) (u v : Signature AlgebraicComplex 1) :
    T.action u ![false]*T.action v ![true] - T.action v ![false]*T.action u ![true] =
      determinant T.matrix*(u ![false]*v ![true]-v ![false]*u ![true]) := by
  simp only [unary_action_apply,determinant]
  ring

theorem unary_action_nonzero (T : InvertibleKernel) (u : Signature AlgebraicComplex 1)
    (hu : u ![false] ≠ 0) : T.action u ![false] ≠ 0 ∨ T.action u ![true] ≠ 0 := by
  by_contra h
  push Not at h
  have hz : determinant T.matrix*u ![false]=0 := by
    simp only [unary_action_apply] at h
    unfold determinant
    linear_combination T.matrix true true*h.1-T.matrix false true*h.2
  exact mul_ne_zero (determinant_ne_zero T) hu hz

/-- Seven realized projective unary directions cannot all map into the six
actual affine unary lines under one invertible matrix. This rejects every
ordinary affine common basis directly, without a candidate enumeration. -/
theorem no_affine_basis {B : InvertibleKernel}
    (hc : InAffineBasis B (cubic (K := AlgebraicComplex)))
    (h0 : InAffineBasis B (StableHigherCurrentAnchorLocalBasis.pin false))
    (hE : Affine (kernelSignature (Kernel.pullback Signature.equality B.matrix))) : False := by
  have hl (i : Fin 7) : ∃ c : AlgebraicComplex, c≠0 ∧
      ∃ q : StableHigherCurrentAnchorAffineBasis.LineCode, ∀ b : Bool,
      B.symm.action (fibonacciUnary i.val) ![b] =
        c*StableHigherCurrentAnchorAffineBasis.line q b :=
    StableHigherCurrentAnchorAffineBasis.unary_line _
      (fibonacciUnary_inBasis hc h0 hE i.val)
      (unary_action_nonzero B.symm _ (fibonacciUnary_first_nonzero i))
  choose c hc' q hq using hl
  have hinj : Function.Injective q := by
    intro i j he
    by_contra hij
    have hz : B.symm.action (fibonacciUnary i.val) ![false]*
        B.symm.action (fibonacciUnary j.val) ![true] -
        B.symm.action (fibonacciUnary j.val) ![false]*
        B.symm.action (fibonacciUnary i.val) ![true] = 0 := by
      rw [hq i false,hq j true,hq j false,hq i true,he]
      ring
    rw [unary_action_minor] at hz
    exact mul_ne_zero (determinant_ne_zero B.symm) (fibonacciUnary_independent i j hij) hz
  have hcard := Fintype.card_le_of_injective q hinj
  norm_num [StableHigherCurrentAnchorAffineBasis.LineCode] at hcard

theorem no_common_affine {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin false⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) :
    ¬CommonTransformable affineClass H := by
  rintro ⟨_,B,hB⟩
  exact no_affine_basis (hB.2 _ hc) (hB.2 _ h0) hB.1

theorem affine_basis_rejected {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin false⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) (B : InvertibleKernel) :
    ¬IsCommonBasis affineClass H B := by
  intro hB
  exact no_affine_basis (hB.2 _ hc) (hB.2 _ h0) hB.1

theorem product_basis_rejected {H : SignatureFamily AlgebraicComplex}
    (heq : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) (B : InvertibleKernel) :
    ¬IsCommonBasis productClass H B := by
  intro hB
  exact cubic_not_product
    (StableHigherCurrentAnchorProductFamily.common_product_basis_literal heq B hB hc)

theorem localAffine_basis_rejected {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin false⟩ : AnySignature AlgebraicComplex) ∈ H)
    (h1 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin true⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) (B : InvertibleKernel) :
    ¬IsCommonBasis localAffineClass H B := by
  intro hB
  have hm := (StableHigherCurrentAnchorLocalBasis.common_basis_monomial B h0 h1 hB).2
  exact full_support_not_localAffine (monomial_action_full_support B.symm hm cubic_ne_zero)
    (hB.2 _ hc)

/-- The exact obstruction consumed by the ordinary finite terminal: every
one of its affine and local-affine candidates is rejected, and the retained
cubic row itself witnesses failure of literal Product. -/
theorem ordinary_obstruction {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin false⟩ : AnySignature AlgebraicComplex) ∈ H)
    (h1 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin true⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) :
    StableHigherCurrentOrdinaryTerminal.Obstruction H := by
  refine ⟨?_,⟨⟨3,cubic⟩,hc,cubic_not_product⟩,?_⟩
  · intro N _ hN
    exact (StableHigherCurrentOrdinaryTerminal.rejected_iff _ _ _).mpr
      (affine_basis_rejected h0 hc _)
  · intro opposite q
    exact (StableHigherCurrentOrdinaryTerminal.rejected_iff _ _ _).mpr
      (localAffine_basis_rejected h0 h1 hc _)

open Holant.LocalDrafts.MainChain

theorem cubic_preprocess {H : SignatureFamily AlgebraicComplex}
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) :
    (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ preprocess H := by
  refine ⟨hc,by decide,?_⟩
  intro hz
  exact cubic_ne_zero (fun _ => false) (congrFun hz (fun _ => false))

/-- A fully proved non-tractable ordinary slice, prior to any hardness
reduction: the criterion is rejected for the actual entire retained family. -/
theorem not_tract {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin false⟩ : AnySignature AlgebraicComplex) ∈ H)
    (h1 : (⟨1,StableHigherCurrentAnchorLocalBasis.pin true⟩ : AnySignature AlgebraicComplex) ∈ H)
    (heq : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex) ∈ H)
    (hc : (⟨3,cubic⟩ : AnySignature AlgebraicComplex) ∈ H) : ¬Tract H := by
  intro ht
  have htest := (StableHigherCurrentOrdinaryTerminal.tract_iff_finite_test h0 h1 heq).mp ht
  have ho := ordinary_obstruction (StableHigherCurrentOrdinaryTerminal.pin_preprocess h0)
    (StableHigherCurrentOrdinaryTerminal.pin_preprocess h1) (cubic_preprocess hc)
  exact (StableHigherCurrentOrdinaryTerminal.obstruction_iff _).mp ho htest.2

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicCriterion
end
