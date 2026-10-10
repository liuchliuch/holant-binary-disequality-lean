import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGeometry
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Systematic free coordinates are selected from actual original ports of an
affine support. Their joint restriction is a genuine bijection, not an assumed
logical chart. Pinnings of the selected coordinates are therefore ordinary
pinnings on the original signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSystematicSupport
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.AffinePatching
open Module
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n : ℕ}

def coordinate (D : BinaryCode n) (j : Fin n) : D →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj j).comp D.subtype

/-- Original coordinate functionals span the whole dual of the support
space, including its zero-dimensional case. -/
theorem coordinate_span (D : BinaryCode n) :
    Submodule.span (ZMod 2) (Set.range (coordinate D))=⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro x hx
  obtain ⟨j,hj⟩ : ∃j,(x : BinaryVector n) j≠0 := by
    by_contra! absent
    exact hx (Subtype.ext (funext absent))
  exact ⟨coordinate D j,⟨j,rfl⟩,hj⟩

/-- A subset of actual ports gives all independent parameters, bijectively.
Every coordinate formula retains its literal original port index. -/
theorem exists_coordinate_equiv (D : BinaryCode n) :
    ∃r : ℕ,∃p : Fin r→Fin n,Function.Injective p ∧
      ∃e : D ≃ₗ[ZMod 2] BinaryVector r,∀x : D,∀i : Fin r,e x i=x.val (p i) := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' (ZMod 2) (coordinate D)
  let : Fintype κ := Fintype.ofInjective a ha
  let b : Basis κ (ZMod 2) (Dual (ZMod 2) D) :=
    Basis.mk hli (by rw [hspan,coordinate_span])
  let e₀ : D ≃ₗ[ZMod 2] (κ→ZMod 2) :=
    (Module.evalEquiv (ZMod 2) D).trans b.dualBasis.equivFun
  have e₀_value (x : D) (i : κ) : e₀ x i=x.val (a i) := by
    change b.dualBasis.equivFun (Module.evalEquiv (ZMod 2) D x) i=_
    rw [Basis.dualBasis_equivFun]
    simp [b,coordinate]
  let t := Fintype.equivFin κ
  let e : D ≃ₗ[ZMod 2] BinaryVector (Fintype.card κ) :=
    e₀.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) t.symm)
  refine ⟨Fintype.card κ,(fun i=>a (t.symm i)),ha.comp t.symm.injective,e,?_⟩
  intro x i
  exact e₀_value x (t.symm i)


/-- A real information set of the original affine support. The encoding
records semantic coordinates; each decoder is an actual original port. -/
structure SystematicSupport (f : Signature AlgebraicComplex n) (r : ℕ) where
  ports : Fin r→Fin n
  injective : Function.Injective ports
  encode : Word r→Word n
  affine : IsAffineMap encode
  free : ∀z i,encode z (ports i)=z i
  supported : ∀z,f (encode z)≠0
  covers : ∀x,f x≠0 → encode (fun i=>x (ports i))=x

/-- Ternary closure selects the support direction and its original-port
information set internally. No rank, support partition or chart is supplied. -/
theorem exists_systematic (f : Signature AlgebraicComplex n) (a : Word n) (ha : f a≠0)
    (ht : ∀x y z : Word n,f x≠0 → f y≠0 → f z≠0 → f (xor (xor x y) z)≠0) :
    ∃r : ℕ,Nonempty (SystematicSupport f r) := by
  classical
  let D := supportDirections f a ha ht
  obtain ⟨r,p,hp,e,he⟩ := exists_coordinate_equiv D
  let L : BinaryVector r→ₗ[ZMod 2] BinaryVector n := D.subtype.comp e.symm.toLinearMap
  let s : BinaryVector r := fun i=>vectorWord a (p i)
  let offset := vectorWord a-L s
  let enc := affineBoolean offset L
  have freeL (v : BinaryVector r) (i : Fin r) : L v (p i)=v i := by
    exact (he (e.symm v) i).symm.trans (congrFun (e.apply_symm_apply v) i)
  have enc_formula (z : Word r) : enc z=wordVector (vectorWord a+L (vectorWord z-s)) := by
    unfold enc affineBoolean offset
    rw [map_sub]
    congr 1
    abel
  have supported (z : Word r) : f (enc z)≠0 := by
    rw [enc_formula]
    exact (e.symm (vectorWord z-s)).property
  have free (z : Word r) (i : Fin r) : enc z (p i)=z i := by
    apply boolEquiv.injective
    change vectorWord (enc z) (p i)=vectorWord z i
    simp only [enc,affineBoolean,vector_word,offset,Pi.add_apply,Pi.sub_apply,freeL,s]
    ring
  refine ⟨r,⟨⟨p,hp,enc,affineBoolean_isAffine offset L,free,supported,?_⟩⟩⟩
  intro x hx
  have mem : vectorWord x-vectorWord a∈D := by
    change f (wordVector (vectorWord a+(vectorWord x-vectorWord a)))≠0
    have cancel : vectorWord a+(vectorWord x-vectorWord a)=vectorWord x := by abel
    rwa [cancel,word_vector]
  let d : D := ⟨vectorWord x-vectorWord a,mem⟩
  have ed : e d=vectorWord (fun i=>x (p i))-s := by
    funext i
    rw [he]
    rfl
  have ld : L (vectorWord (fun i=>x (p i))-s)=vectorWord x-vectorWord a := by
    rw [←ed]
    change ((e.symm (e d) : D) : BinaryVector n)=_
    rw [e.symm_apply_apply]
  rw [enc_formula,ld]
  have cancel : vectorWord a+(vectorWord x-vectorWord a)=vectorWord x := by abel
  rw [cancel,word_vector]

/-- Squared Affine membership gives the required ternary support geometry,
then selects free coordinates from the same original unsquared signature. -/
theorem exists_of_affine_square (f : Signature AlgebraicComplex n)
    (square : Affine (fun x=>f x^2)) (nonzero : f≠0) :
    ∃r : ℕ,Nonempty (SystematicSupport f r) := by
  obtain ⟨a,ha⟩ := OrdinaryNegativeAffineSquareSupport.exists_base f nonzero
  apply exists_systematic f a ha
  intro x y z hx hy hz
  have h := Holant.ReedMuller.AffinePatching.affine_support_ternary
    (fun x=>f x^2) square x y z (pow_ne_zero 2 hx) (pow_ne_zero 2 hy) (pow_ne_zero 2 hz)
  exact (pow_ne_zero_iff (by decide : 2≠0)).mp h

namespace SystematicSupport
variable {r : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)

def reduced : Signature AlgebraicComplex r := fun z=>f (D.encode z)

theorem reduced_full : ∀z,D.reduced z≠0 := D.supported

theorem reduced_affine (h : Affine f) : Affine D.reduced := h.precompose D.encode D.affine

/-- Class reflection uses actual coordinate projection and the original
support equations; it never installs the compressed row as a physical gate. -/
theorem affine_of_reduced (S : AffineSystem n) (support : ∀x,S.Holds x ↔ f x≠0)
    (h : Affine D.reduced) : Affine f := by
  have hc := (h.precompose (fun x i=>x (D.ports i)) (coordinates_isAffineMap D.ports)).restrict S
  convert hc using 1
  funext x
  by_cases hx : f x≠0
  · simp only [ite_eq_left ((support x).mpr hx),reduced,D.covers x hx]
  · simp only [ite_eq_right (mt (support x).mp hx)]
    exact not_ne_iff.mp hx

theorem nonAffine_reduced (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f) : ¬Affine D.reduced := by
  intro ha
  obtain ⟨S,hS⟩ := OrdinaryNegativeAffineSquareSupport.exists_support_system f square nonzero
  exact bad (D.affine_of_reduced S hS ha)


/-- The selected rank is witnessed by an exact enumeration of all supported
assignments, including rank zero. -/
def supportEquiv : Word r ≃ {x : Word n // f x≠0} where
  toFun z := ⟨D.encode z,D.supported z⟩
  invFun x := fun i=>x.val (D.ports i)
  left_inv z := funext (D.free z)
  right_inv x := Subtype.ext (D.covers x.val x.property)

include D in
theorem support_card : Fintype.card {x : Word n // f x≠0}=2^r := by
  classical
  rw [←Fintype.card_congr D.supportEquiv]
  simp [Word]

end SystematicSupport

theorem affine_map_comp {r m : ℕ} (p : Word m→Word n) (q : Word r→Word m)
    (hp : IsAffineMap p) (hq : IsAffineMap q) : IsAffineMap (fun x=>p (q x)) := by
  unfold IsAffineMap at hp hq ⊢
  intro x y
  simp only [hq,hp]
  funext i
  simp only [AffinePhase.xor]
  generalize p (q x) i=a
  generalize p (q y) i=b
  generalize p (q (origin r)) i=c
  generalize p (origin m) i=d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

def pinMask (f : Signature AlgebraicComplex n) (j : Fin n) (b : Bool) : Signature AlgebraicComplex n :=
  fun x=>if x j=b then f x else 0

/-- Pinning one selected actual original port removes precisely one free
coordinate. The remaining free ports keep their original names. -/
def SystematicSupport.pinFirst {r : ℕ} {f : Signature AlgebraicComplex n}
    (D : SystematicSupport f (r+1)) (b : Bool) :
    SystematicSupport (pinMask f (D.ports 0) b) r where
  ports j := D.ports j.succ
  injective := D.injective.comp (Fin.succ_injective r)
  encode z := D.encode (Fin.cons b z)
  affine := affine_map_comp D.encode (fun z : Word r=>Fin.cons b z) D.affine (cons_isAffineMap b)
  free z i := by simpa using D.free (Fin.cons b z) i.succ
  supported z := by simpa only [pinMask,D.free,Fin.cons_zero,ite_true] using D.supported (Fin.cons b z)
  covers x hx := by
    have xb : x (D.ports 0)=b := by
      by_contra he
      exact hx (by simp [pinMask,he])
    have hf : f x≠0 := by simpa only [pinMask,ite_eq_left xb] using hx
    have word : Fin.cons b (fun j=>x (D.ports j.succ))=(fun i=>x (D.ports i)) := by
      funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · exact xb.symm
      · rfl
    rw [word]
    exact D.covers x hf

/-- Both values of any selected first port have exactly half the original
support, even when the original support has arbitrary dependent columns. -/
theorem SystematicSupport.pinFirst_card {r : ℕ} {f : Signature AlgebraicComplex n}
    (D : SystematicSupport f (r+1)) (b : Bool) :
    Fintype.card {x : Word n // pinMask f (D.ports 0) b x≠0}=2^r :=
  (D.pinFirst b).support_card


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSystematicSupport
end
