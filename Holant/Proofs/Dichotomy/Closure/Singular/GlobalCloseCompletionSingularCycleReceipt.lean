import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularCubicCycle

/-! Keep the actual four-cycle scalar and the canonical dense normalization.
The radius satisfies r²=B/A and its normalization root satisfies u²=2r.
The returned basis is literally denseNormalization r u, so later diagonal
phase resources can be transported in this same basis without a new choice. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularCycleReceipt
open Holant Holant.Tractable
open Holant.EightVertex.ProductAnchor
open GlobalCloseCompletionSingularCubicCycle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
set_option maxRecDepth 16384
set_option Elab.async false

abbrev rho (A B : Scalar) : Scalar := 2*A^2*B^2
abbrev zeroWord : Word4 := fun _=>false

theorem radius_exists (A B : Scalar) (hA : A≠0) (hB : B≠0) :
    ∃r : Scalar,r≠0 ∧ r^2=B/A := by
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq ((B/A : Scalar) : ℂ) (by decide : 0<2)
  let r : Scalar := ⟨v,IsIntegral.of_pow (n:=2) (by decide) (by
    rw [hv]
    exact (B/A : Scalar).property)⟩
  have hr2 : r^2=B/A := Subtype.ext hv
  refine ⟨r,?_,hr2⟩
  intro zero
  exact (div_ne_zero hB hA) (by simpa [zero] using hr2.symm)

theorem cycle_literal (A B r : Scalar) (hA : A≠0) (hr2 : r^2=B/A) :
    cycle (cubic A B)=denseTensor (rho A B) r zeroWord := by
  have hr4 : r^4=(B/A)^2 := by
    calc r^4=(r^2)^2 := by ring
         _=(B/A)^2 := by rw [hr2]
  funext x
  rw [cycle_value]
  have hx : x=![x 0,x 1,x 2,x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  generalize x 0=a, x 1=b, x 2=c, x 3=d
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [denseTensor, rho, zeroWord, weight_four, bitSign, hr2, hr4] <;>
    field_simp [hA]

structure Receipt (F : SignatureFamily Scalar) (A B : Scalar) where
  r : Scalar
  u : Scalar
  r_nonzero : r≠0
  u_nonzero : u≠0
  r_square : r^2=B/A
  u_square : u^2=2*r
  scale : Scalar
  scale_nonzero : scale≠0
  dense_literal : cycle (cubic A B)=denseTensor (rho A B) r zeroWord
  actual : Gadget.Realizes F .disequality (fun x=>scale*cycle (cubic A B) x)

variable {F : SignatureFamily Scalar} {A B : Scalar}

def Receipt.basis (d : Receipt F A B) : InvertibleKernel :=
  denseNormalization d.r d.u d.r_nonzero d.u_nonzero

def Receipt.output (d : Receipt F A B) : Signature Scalar 4 :=
  fun x=>d.scale*cycle (cubic A B) x

abbrev Receipt.coefficient (d : Receipt F A B) : Scalar :=
  d.scale*denseNormalizationScale (rho A B) d.u zeroWord

theorem Receipt.edge (d : Receipt F A B) :
    Kernel.pullback Signature.disequality d.basis.inverse=Signature.equality :=
  normalization_edge d.r d.u d.u_nonzero d.u_square

theorem Receipt.normalized (d : Receipt F A B) :
    d.basis.action d.output=fun x=>d.coefficient*equalityFour x := by
  change Signature.coordinateAction (fun _=>normalizationMatrix d.r d.u)
    (fun x=>d.scale*cycle (cubic A B) x)=_
  rw [coordinateAction_scale,d.dense_literal,normalize_denseTensor _ _ _ d.r_nonzero]
  rw [normalized_eq_equality_of_endpoint zeroWord (Or.inl (by decide))]
  funext x
  change d.scale*(denseNormalizationScale (rho A B) d.u zeroWord*equalityFour x)=
    (d.scale*denseNormalizationScale (rho A B) d.u zeroWord)*equalityFour x
  ring

theorem Receipt.coefficient_nonzero (d : Receipt F A B) (hA : A≠0) (hB : B≠0) :
    d.coefficient≠0 :=
  mul_ne_zero d.scale_nonzero (denseNormalizationScale_ne_zero _ _ _
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hB)) d.u_nonzero)

theorem Receipt.coefficient_literal (d : Receipt F A B) (hA : A≠0) :
    d.coefficient=4*d.scale*A*B^3 := by
  have hu4 : d.u^4=4*(B/A) := by
    calc d.u^4=(d.u^2)^2 := by ring
         _=(2*d.r)^2 := by rw [d.u_square]
         _=4*d.r^2 := by ring
         _=4*(B/A) := by rw [d.r_square]
  simp only [Receipt.coefficient, denseNormalizationScale,
    weight_zero_four, pow_zero, mul_one, hu4, rho]
  field_simp [hA]

theorem Receipt.anchor (d : Receipt F A B) (hA : A≠0) (hB : B≠0) :
    HasEqualityAnchor F := by
  refine ⟨d.output,d.basis,1,d.coefficient,one_ne_zero,
    d.coefficient_nonzero hA hB,d.actual,?_,d.normalized⟩
  simpa using d.edge

theorem produce (F : SignatureFamily Scalar) (A B : Scalar) (hA : A≠0) (hB : B≠0)
    (actual : Gadget.Realizes F .disequality (cubic A B)) : Nonempty (Receipt F A B) := by
  obtain ⟨r,hr,hsq⟩ := radius_exists A B hA hB
  obtain ⟨u,hu,hu2⟩ := exists_algebraic_normalizing_root r hr
  obtain ⟨c,hc,realized⟩ := cycle_realizes F (cubic A B) actual
  exact ⟨⟨r,u,hr,hu,hsq,hu2,c,hc,cycle_literal A B r hA hsq,realized⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularCycleReceipt
end
