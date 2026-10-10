import Holant.Certificates.TetrahedralEightPort.SafeAffine

/-! No nonzero vector in the genuine six-port safe cone has a unary factor.
The obstruction is transported through the actual local matrix actions and
permutations, with arbitrary nonzero complex exterior scales. -/
namespace Holant.Platonic.TetrahedralEightPortBase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Certificates.MatchingProductBridge
open Holant.Platonic.StabilizerLine
open Holant.Certificates.TetrahedralEightPort.OrbitActions
open Holant.Certificates.TetrahedralEightPort.SafeAffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Literal unary separation on the physical port `p`; the second function is
proved independent of that coordinate. Zero factors are permitted. -/
def SeparatesAt {n : ℕ} (p : Fin n) (f : Signature ℂ n) : Prop :=
  ∃ u : Bool → ℂ, ∃ v : Signature ℂ n,
    (∀ x b, v (Function.update x p b) = v x) ∧
    ∀ x, f x = u (x p) * v x

theorem SeparatesAt.scale {n : ℕ} {p : Fin n} {f : Signature ℂ n}
    (h : SeparatesAt p f) (c : ℂ) : SeparatesAt p (c • f) := by
  obtain ⟨u,v,hv,he⟩ := h
  refine ⟨fun b => c*u b,v,hv,?_⟩
  intro x
  simp only [Pi.smul_apply,smul_eq_mul,he]
  ring

theorem SeparatesAt.minor {n : ℕ} {p : Fin n} {f : Signature ℂ n}
    (h : SeparatesAt p f) (x y : Word n) :
    f x * f y = f (Function.update x p (y p)) * f (Function.update y p (x p)) := by
  obtain ⟨u,v,hv,he⟩ := h
  simp only [he,Function.update_self,hv]
  ring

theorem SeparatesAt.local {p q : Fin 6} {f : SixTensor}
    (h : SeparatesAt p f) (M : Matrix2) : SeparatesAt p (localLinear q M f) := by
  obtain ⟨u,v,hv,he⟩ := h
  by_cases hpq : p=q
  · subst q
    refine ⟨fun a => ∑ b : Bool, M a b*u b,v,hv,?_⟩
    intro x
    simp only [localLinear,LinearMap.coe_mk,AddHom.coe_mk,he,Function.update_self,hv,
      Fintype.sum_bool]
    ring
  · refine ⟨u,localLinear q M v,?_,?_⟩
    · intro x b
      simp only [localLinear,LinearMap.coe_mk,AddHom.coe_mk,
        Function.update_of_ne (Ne.symm hpq)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Function.update_comm hpq,hv]
    · intro x
      simp only [localLinear,LinearMap.coe_mk,AddHom.coe_mk,he,
        Function.update_of_ne hpq,Fintype.sum_bool]
      ring

theorem SeparatesAt.permute {p : Fin 6} {f : SixTensor}
    (h : SeparatesAt p f) (e : Equiv.Perm (Fin 6)) :
    SeparatesAt (e p) (portLinear e f) := by
  obtain ⟨u,v,hv,he⟩ := h
  refine ⟨u,portLinear e v,?_,?_⟩
  · intro x b
    change v (fun j => Function.update x (e p) b (e j)) = v (fun j=>x (e j))
    have hh : (fun j => Function.update x (e p) b (e j)) =
        Function.update (fun j=>x (e j)) p b := by
      funext j
      by_cases hj : j=p
      · subst j; simp
      · simp [Function.update_of_ne hj,Function.update_of_ne (e.injective.ne hj)]
    rw [hh,hv]
  · intro x
    exact he (fun j=>x (e j))

def NoUnary (f : SixTensor) : Prop := ∀ p, ¬SeparatesAt p f

theorem noUnary_scale {f : SixTensor} (hf : NoUnary f) (c : ℂ) (hc : c≠0) :
    NoUnary (c • f) := by
  intro p hp
  have h := hp.scale c⁻¹
  simp only [smul_smul,inv_mul_cancel₀ hc,one_smul] at h
  exact hf p h

theorem noUnary_local {f : SixTensor} (hf : NoUnary f) (p : Fin 6) (M : Matrix2)
    (hM : M.det≠0) : NoUnary (localLinear p M f) := by
  intro q hq
  have h := hq.local (q:=p) M⁻¹
  rw [local_mul,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),local_one] at h
  exact hf q h

theorem noUnary_permute {f : SixTensor} (hf : NoUnary f) (e : Equiv.Perm (Fin 6)) :
    NoUnary (portLinear e f) := by
  intro p hp
  have h := hp.permute e.symm
  change SeparatesAt (e.symm p) (Tensor.reindex e.symm (Tensor.reindex e f)) at h
  rw [Tensor.reindex_symm] at h
  exact hf _ h

set_option maxHeartbeats 1000000 in
theorem M0_noUnary : NoUnary M0 := by
  intro p hp
  have h := hp.minor (fun _=>false) (fun _=>true)
  fin_cases p <;>
    norm_num [M0,Q0,Signature.equality,Function.update] at h

set_option maxHeartbeats 2000000 in
theorem H0_noUnary : NoUnary H0 := by
  have h6 : (6 : ZMod 2)=0 := by decide
  intro p hp
  have h := hp.minor (fun _=>false) (fun _=>true)
  rw [SafeAffineH_formula] at h
  fin_cases p <;>
    norm_num [complexAffineFormula,SafeAffineHSystem_holds,SafeAffineHPhase_eval,
      bitValue,fourthRootPhase,Function.update,ZMod.val_natCast,ZMod.val_ofNat,
      ZMod.val_zero,ZMod.natCast_self,Complex.I_sq,h6] at h <;> exact h h6

def NoUnaryPoint (q : Point) : Prop :=
  ∃ f : SixTensor, ∃ hf : f≠0, Projectivization.mk ℂ f hf=q ∧ NoUnary f

theorem noUnary_representative {q : Point} (hq : NoUnaryPoint q)
    (f : SixTensor) (hf : f≠0) (he : Projectivization.mk ℂ f hf=q) : NoUnary f := by
  obtain ⟨g,hg,hgq,hgn⟩ := hq
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ f g hf hg).mp (he.trans hgq.symm)
  have hcn : c≠0 := by intro hz; apply hf; rw [←hc,hz,zero_smul]
  rw [←hc]
  exact noUnary_scale hgn c hcn

theorem noUnary_actual_step (a : ActualOperation) (q : Point)
    (hq : NoUnaryPoint q) : NoUnaryPoint (actualStep a q) := by
  obtain ⟨f,hf,rfl,hfn⟩ := hq
  cases a with
  | dress p M hM =>
    refine ⟨localLinear p M f,?_,rfl,
      noUnary_local hfn p M (groupDirection_det_ne_zero .tetrahedral hM)⟩
    intro hz
    exact hf (local_injective p M (groupDirection_det_ne_zero .tetrahedral hM)
      (by simpa using hz))
  | permute e =>
    refine ⟨portLinear e f,?_,rfl,noUnary_permute hfn e⟩
    intro hz
    exact hf (port_injective e (by simpa using hz))

theorem noUnary_orbit {base q : Point} (hb : NoUnaryPoint base)
    (hq : q∈ActualOrbit base) : NoUnaryPoint q := by
  induction hq with
  | base => exact hb
  | next a h ih => exact noUnary_actual_step a _ ih

theorem safeCone_noUnary (f : SixTensor) (hf : SafeCone f) (hn : f≠0) : NoUnary f := by
  rcases hf with hz|⟨hz,hp⟩
  · exact False.elim (hn hz)
  · apply noUnary_representative (f:=f) (hf:=hn) (he:=rfl)
    rcases hp with hm|hh
    · exact noUnary_orbit ⟨M0,M0_ne_zero,rfl,M0_noUnary⟩ hm
    · exact noUnary_orbit ⟨H0,H0_ne_zero,rfl,H0_noUnary⟩ hh

end
end Holant.Platonic.TetrahedralEightPortBase
