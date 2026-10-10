import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsCaps
import Holant.Projective.BoundedTorsion.CyclotomicDegree
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic

/-! The actual native antidiagonal ratios form a subgroup, using the native
edge box, genuine reversed gadgets and native series. If every such ratio
has finite order, the original number field makes this subgroup finite.
The selected generator supplies every root of its exact order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeAntiGroup
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Projective.BoundedTorsion
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace R
export PaperTerminalBridgeEqualProductsCaps (Rel refl symm unscale)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def Available (F : SignatureFamily K) (t : K) : Prop := R.Rel F 1 t

theorem one (F : SignatureFamily K) : Available F 1 := R.refl F 1 one_ne_zero

theorem mul (F : SignatureFamily K) (s t : K) (hs : Available F s) (ht : Available F t) :
    Available F (s*t) := by
  obtain ⟨c,hc,actualC⟩ := hs
  obtain ⟨d,hd,actualD⟩ := ht
  have actual := realizes_splice F (fun x=>c*C.antiTensor 1 s x)
    (fun x=>d*C.antiTensor 1 t x) actualC actualD 0
  refine ⟨c*d,mul_ne_zero hc hd,?_⟩
  convert actual using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [spliceTensor,C.antiTensor,Signature.disequality,h0,h1,Function.update] <;> ring

theorem inv (F : SignatureFamily K) (t : K) (nonzero : t≠0) (ht : Available F t) :
    Available F t⁻¹ := by
  have h := R.symm F 1 t ht
  apply R.unscale F (C.antiTensor 1 t⁻¹) t nonzero
  have value : (fun x=>t*C.antiTensor 1 t⁻¹ x)=C.antiTensor t 1 := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [C.antiTensor,h0,h1,nonzero]
  rw [value]
  exact h

def group (F : SignatureFamily K) : Subgroup Kˣ where
  carrier := {u | Available F (u:K)}
  one_mem' := one F
  mul_mem' := fun hu hv=>mul F _ _ hu hv
  inv_mem' := by
    intro u hu
    change Available F ((u⁻¹:Kˣ):K)
    rw [Units.val_inv_eq_inv_val]
    exact inv F _ (Units.ne_zero _) hu

theorem group_pow (F : SignatureFamily K) (u : group F) (n : ℕ) :
    Available F ((u.val:K)^n) := by
  exact (u^n).property

variable [NumberField K]

theorem torsion_bound (t : K) (h : IsOfFinOrder t) :
    t^torsionExponent (Module.finrank ℚ K)=1 := by
  apply pow_torsionExponent h
  exact totient_le_twice_degree_of_add_inv (L:=K) (E:=K)
    h.orderOf_pos (IsPrimitiveRoot.orderOf t) (s:=t+t⁻¹) (by simp)

theorem finite (F : SignatureFamily K)
    (torsion : ∀t : K,Available F t→t≠0→IsOfFinOrder t) : Finite (group F) := by
  let e := torsionExponent (Module.finrank ℚ K)
  have roots : {t : K | t^e=1}.Finite := finite_power_fiber (torsionExponent_pos _) 1
  let f : group F→{t : K | t^e=1} := fun u=>
    ⟨u.val,torsion_bound _ (torsion _ u.property (Units.ne_zero _))⟩
  letI : Finite {t : K | t^e=1} := roots
  exact Finite.of_injective f (by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h)

theorem complete (F : SignatureFamily K)
    (torsion : ∀t : K,Available F t→t≠0→IsOfFinOrder t) :
    ∃m : ℕ,0<m ∧ ∃g : K,IsPrimitiveRoot g m ∧
      (∀n : ℕ,Available F (g^n)) ∧
      (∀t : K,t^m=1↔(t≠0 ∧ Available F t)) := by
  letI : Finite (group F) := finite F torsion
  let f : group F→*K := (Units.coeHom K).comp (group F).subtype
  have injective : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    exact Units.ext h
  letI : IsCyclic (group F) := isCyclic_of_injective_ringHom f injective
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α:=group F)
  let m := Nat.card (group F)
  have positive : 0<m := Nat.card_pos
  have primitive : IsPrimitiveRoot (f u) m := by
    change IsPrimitiveRoot (f u) (Nat.card (group F))
    rw [←hu]
    exact (IsPrimitiveRoot.orderOf u).map_of_injective injective
  refine ⟨m,positive,f u,primitive,fun n=>group_pow F u n,?_⟩
  intro t
  constructor
  · intro root
    letI : NeZero m := ⟨Nat.ne_of_gt positive⟩
    obtain ⟨n,_bound,rfl⟩ := primitive.eq_pow_of_pow_eq_one root
    exact ⟨pow_ne_zero _ (primitive.ne_zero positive.ne'),group_pow F u n⟩
  · rintro ⟨nonzero,actual⟩
    let v : group F := ⟨Units.mk0 t nonzero,actual⟩
    have h : v^Nat.card (group F)=1 := pow_card_eq_one'
    exact congrArg f h


theorem complete_mapped (F : SignatureFamily K) (φ : K→+*ℂ)
    (torsion : ∀t : K,Available F t→t≠0→IsOfFinOrder t) :
    ∃m : ℕ,0<m ∧
      (∀t : K,t≠0→Available F t→φ t^m=1) ∧
      (∀z : ℂ,z^m=1→∃t : K,t≠0 ∧ Available F t ∧ φ t=z) := by
  obtain ⟨m,positive,g,primitive,powers,exact⟩ := complete F torsion
  have mapped : IsPrimitiveRoot (φ g) m := primitive.map_of_injective φ.injective
  refine ⟨m,positive,?_,?_⟩
  · intro t nonzero actual
    simpa only [map_pow,map_one] using congrArg φ ((exact t).mpr ⟨nonzero,actual⟩)
  · intro z root
    letI : NeZero m := ⟨Nat.ne_of_gt positive⟩
    obtain ⟨n,_bound,rfl⟩ := mapped.eq_pow_of_pow_eq_one root
    exact ⟨g^n,pow_ne_zero _ (primitive.ne_zero positive.ne'),powers n,map_pow φ g n⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeAntiGroup
end
