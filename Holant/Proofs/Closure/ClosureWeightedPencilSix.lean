import Holant.Proofs.Closure.ClosureWeightedPencilAnalytic
import Holant.Proofs.Closure.ClosureSixPortBase

/-! All original six-port orders and both parity pencils. The deleted-port
delta correction is explicit. The enlarged ordinary deck is solely analytic;
no additional phase representative or gadget resource is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain ClosureRootPencil

def algebraicSlice (h : Signature Scalar 6) (e : Equiv.Perm (Fin 6)) (p a : Bool) :
    Signature Scalar 4 := fun x => h (ClosureSixPort.fillSix e a p x)

def complexSix (h : Signature Scalar 6) : Signature ℂ 6 := fun x => (h x : ℂ)

def weightedSixCard (h : Signature Scalar 6) (d : Scalar)
    (e : Equiv.Perm (Fin 6)) (p : Bool) (t : Scalar) : Signature Scalar 4 :=
  Signature.contract (Kernel.mul (ClosureShiftedWeighted.D d) (if p then S t else R t))
    (Tensor.reindex e.symm h)

def weightedEndpoints (h : Signature Scalar 6) (d : Scalar)
    (e : Equiv.Perm (Fin 6)) (p : Bool) : Signature Scalar 4 × Signature Scalar 4 :=
  if p then (d • algebraicSlice h e p true,algebraicSlice h e p false)
  else (algebraicSlice h e p false,d • algebraicSlice h e p true)

theorem weightedSixCard_pencil (h : Signature Scalar 6) (d : Scalar)
    (e : Equiv.Perm (Fin 6)) (p : Bool) (t : Scalar) :
    weightedSixCard h d e p t=
      algebraicPencil (weightedEndpoints h d e p).1 (weightedEndpoints h d e p).2 t := by
  funext x
  cases p <;>
    simp [weightedSixCard,weightedEndpoints,algebraicPencil,algebraicSlice,
      ClosureSixPort.fillSix,ClosureShiftedWeighted.D,Signature.contract,
      Kernel.mul_apply,diagonalKernel,R,S,Signature.disequality,
      Tensor.reindex,Fintype.sum_bool]
  · change d*t*h (fun i => (Fin.cons true (Fin.cons true x) : Fin 6 → Bool) (e.symm i))+
      h (fun i => (Fin.cons false (Fin.cons false x) : Fin 6 → Bool) (e.symm i))=
      h (fun i => (Fin.cons false (Fin.cons false x) : Fin 6 → Bool) (e.symm i))+
        t*(d*h (fun i => (Fin.cons true (Fin.cons true x) : Fin 6 → Bool) (e.symm i)))
    ring
  · change d*h (fun i => (Fin.cons true (Fin.cons false x) : Fin 6 → Bool) (e.symm i))+
      t*h (fun i => (Fin.cons false (Fin.cons true x) : Fin 6 → Bool) (e.symm i))=
      d*h (fun i => (Fin.cons true (Fin.cons false x) : Fin 6 → Bool) (e.symm i))+
        t*h (fun i => (Fin.cons false (Fin.cons true x) : Fin 6 → Bool) (e.symm i))
    rfl

def WeightedSixDeck (m : ℕ) (d : Scalar) (h : Signature Scalar 6) : Prop :=
  ∀ e : Equiv.Perm (Fin 6),∀ p : Bool,∀ t : Phase m,
    weightedSixCard h d e p t.val=0 ∨ WeightedMatching m d (weightedSixCard h d e p t.val)

theorem delta_double_root {m : ℕ} {d : Scalar} (square : Roots m (d^2)) :
    (d : ℂ)^(2*m)=1 := by
  have scalar : d^(2*m)=1 := by rw [pow_mul];exact square
  exact_mod_cast scalar

theorem corrected_even (h : Signature Scalar 6) (d : Scalar) (hd : d≠0)
    (e : Equiv.Perm (Fin 6)) (s : ℂ) :
    ClosureSixPort.phaseCard (complexSix h) e false s=
      pencil (complexTensor (weightedEndpoints h d e false).1)
        (complexTensor (weightedEndpoints h d e false).2) (s/(d : ℂ)) := by
  have dc : (d : ℂ)≠0 := by exact_mod_cast hd
  funext x
  change (h (ClosureSixPort.fillSix e false false x) : ℂ)+
    s*(h (ClosureSixPort.fillSix e true false x) : ℂ)=
    (h (ClosureSixPort.fillSix e false false x) : ℂ)+
      (s/(d : ℂ))*((d* h (ClosureSixPort.fillSix e true false x) : Scalar) : ℂ)
  change _+s*_=_+(s/(d : ℂ))*
    CyclicBoundary.AlgebraicRepresentatives.inclusion (d*h (ClosureSixPort.fillSix e true false x))
  rw [map_mul]
  change (h (ClosureSixPort.fillSix e false false x) : ℂ)+
    s*(h (ClosureSixPort.fillSix e true false x) : ℂ)=
    (h (ClosureSixPort.fillSix e false false x) : ℂ)+
      (s/(d : ℂ))*((d : ℂ)*(h (ClosureSixPort.fillSix e true false x) : ℂ))
  field_simp [dc]
  <;> ring

theorem corrected_odd (h : Signature Scalar 6) (d : Scalar) (hd : d≠0)
    (e : Equiv.Perm (Fin 6)) (s : ℂ) (hs : s≠0) :
    ClosureSixPort.phaseCard (complexSix h) e true s=
      (s/(d : ℂ)) • pencil (complexTensor (weightedEndpoints h d e true).1)
        (complexTensor (weightedEndpoints h d e true).2) ((d : ℂ)/s) := by
  have dc : (d : ℂ)≠0 := by exact_mod_cast hd
  funext x
  change (h (ClosureSixPort.fillSix e false true x) : ℂ)+
    s*(h (ClosureSixPort.fillSix e true true x) : ℂ)=
    (s/(d : ℂ))*
      (((d*h (ClosureSixPort.fillSix e true true x) : Scalar) : ℂ)+
        ((d : ℂ)/s)*(h (ClosureSixPort.fillSix e false true x) : ℂ))
  change _+s*_=(s/(d : ℂ))*(
    CyclicBoundary.AlgebraicRepresentatives.inclusion (d*h (ClosureSixPort.fillSix e true true x))+_)
  rw [map_mul]
  change (h (ClosureSixPort.fillSix e false true x) : ℂ)+
    s*(h (ClosureSixPort.fillSix e true true x) : ℂ)=
    (s/(d : ℂ))*((d : ℂ)*(h (ClosureSixPort.fillSix e true true x) : ℂ)+
      ((d : ℂ)/s)*(h (ClosureSixPort.fillSix e false true x) : ℂ))
  field_simp [dc,hs]
  <;> ring

/-- A full ordinary analytic deck at order 2m follows internally from every
actual weighted order/parity sample. Its new phases have no physical claim. -/
theorem analytic_ordered_deck {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (h : Signature Scalar 6) (deck : WeightedSixDeck m d h) :
    ClosureSixPort.OrderedRootDeck (2*m) (complexSix h) := by
  intro e p s root
  have dr := delta_double_root square
  have dc : (d : ℂ)≠0 := by exact_mod_cast hd
  have sn : s≠0 := by
    intro zero
    rw [zero,zero_pow (by omega : 2*m≠0)] at root
    norm_num at root
  have samples : ∀ t : Phase m,
      algebraicPencil (weightedEndpoints h d e p).1 (weightedEndpoints h d e p).2 t.val=0 ∨
      WeightedMatching m d
        (algebraicPencil (weightedEndpoints h d e p).1 (weightedEndpoints h d e p).2 t.val) := by
    intro t
    simpa only [weightedSixCard_pencil] using deck e p t
  have enlarged := weighted_all_double hm d hd square _ _ samples
  cases p
  · have phase : (s/(d : ℂ))^(2*m)=1 := by rw [div_pow,root,dr,div_self one_ne_zero]
    rw [corrected_even h d hd e s]
    exact (enlarged _ phase).imp id (rootMatching_iff_product (2*m) _).mpr
  · have phase : ((d : ℂ)/s)^(2*m)=1 := by rw [div_pow,dr,root,div_self one_ne_zero]
    rw [corrected_odd h d hd e s sn]
    rcases enlarged _ phase with zero | actual
    · left;rw [zero,smul_zero]
    · right
      exact (rootMatching_iff_product (2*m) _).mpr
        (product_scale actual _ (div_ne_zero sn dc))

theorem weighted_six_split {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (h : Signature Scalar 6) (nonzero : h≠0)
    (deck : WeightedSixDeck m d h) : ClosureSixPort.PrimitiveSixSplit (complexSix h) := by
  have live : complexSix h≠0 := by
    intro zero
    apply nonzero
    funext x
    have point : (h x : ℂ)=0 := congrFun zero x
    exact_mod_cast point
  exact ClosureSixPort.direct_six_port_split (by omega : 3≤2*m) _ live
    (analytic_ordered_deck hm d hd square h deck)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
