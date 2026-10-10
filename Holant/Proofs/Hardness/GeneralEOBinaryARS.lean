import Holant.Proofs.Hardness.GeneralEOARSBoundary

/-! For a centrally supported binary, and only at this binary arity,
equal opposite norms characterize ARS up to a nonzero scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryARS
open Holant
namespace A
export GeneralEOARSBoundary (ARSUpToScale binary_equal_norm)
end A
namespace F
export SelfDualPinObstruction (flip)
end F
set_option backward.isDefEq.respectTransparency false

theorem exists_scale (p q : ℂ) (hn : ‖p‖=‖q‖) :
    ∃c : ℂ,c≠0 ∧ q/c=star (p/c) := by
  classical
  have hm : p*star p=q*star q := by
    simp only [Complex.star_def,Complex.mul_conj',hn]
  by_cases hp : p=0
  · have hq : q=0 := norm_eq_zero.mp (by simpa [hp] using hn.symm)
    exact ⟨1,one_ne_zero,by simp [hp,hq]⟩
  by_cases hs : p+q=0
  · have hd : p-q≠0 := by
      intro he
      have hz : p=0 := by linear_combination (1/2 : ℂ)*hs+(1/2 : ℂ)*he
      exact hp hz
    let c : ℂ := Complex.I*(p-q)
    have hc : c≠0 := mul_ne_zero Complex.I_ne_zero hd
    refine ⟨c,hc,?_⟩
    rw [star_div₀]
    apply (div_eq_div_iff hc (star_ne_zero.mpr hc)).mpr
    simp only [c,star_mul,star_sub,Complex.star_def,Complex.conj_I]
    simp only [Complex.star_def] at hm
    linear_combination -Complex.I*hm
  · refine ⟨p+q,hs,?_⟩
    rw [star_div₀]
    apply (div_eq_div_iff hs (star_ne_zero.mpr hs)).mpr
    simp only [star_add]
    linear_combination -hm

theorem ars_of_equal_norm (f : Signature ℂ 2)
    (hE : Signature.CentralSupport f)
    (hn : ‖f ![false,true]‖=‖f ![true,false]‖) : A.ARSUpToScale f := by
  obtain ⟨c,hc,hcval⟩ := exists_scale (f ![false,true]) (f ![true,false]) hn
  have hreverse : f ![false,true]/c=star (f ![true,false]/c) := by
    simpa only [star_star] using (congrArg star hcval).symm
  have h00 : f ![false,false]=0 := hE _ (by decide)
  have h11 : f ![true,true]=0 := hE _ (by decide)
  refine ⟨c,hc,fun x=>f x/c,?_,?_⟩
  · intro x
    have hx : x=![x 0,x 1] := by
      funext i
      fin_cases i <;> rfl
    have hf (u v : Bool) : F.flip (![u,v] : Fin 2→Bool)=![!u,!v] := by
      funext i
      fin_cases i <;> rfl
    change f (F.flip x)/c=star (f x/c)
    rw [hx,hf]
    cases x 0 <;> cases x 1 <;>
      first | exact hcval | exact hreverse | simp [h00,h11]
  · funext x
    change f x=c*(f x/c)
    field_simp

theorem ars_iff_equal_norm (f : Signature ℂ 2) (hE : Signature.CentralSupport f) :
    A.ARSUpToScale f ↔ ‖f ![false,true]‖=‖f ![true,false]‖ :=
  ⟨A.binary_equal_norm f,ars_of_equal_norm f hE⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryARS
