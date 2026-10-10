import Holant.Proofs.Hardness.SelfDualPinObstruction
import Holant.Proofs.Hardness.GeneralGeometricCapLocal

/-! Complex conjugate reversal is preserved by actual finite networks.
This blocks a particular local directed-pin strategy, not global oracle
reductions or counting hardness. Loops, parallel edges and ordered ports are
retained in the explicit edge-end assignment involution. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConjugatePinObstruction
open Holant
open scoped BigOperators
namespace F
export SelfDualPinObstruction (flip flip_flip flipEquiv assignment_flip oriented01)
end F

variable {K : Type*} [CommSemiring K]

def Reversal (σ : K →+* K) {n : ℕ} (f : Signature K n) : Prop :=
  ∀x,f (F.flip x)=σ (f x)

theorem term_reversal (σ : K →+* K) {n : ℕ} (N : Network K n)
    (hv : ∀v,Reversal σ (N.vertex v))
    (he : ∀e a b,N.edge e (!a) (!b)=σ (N.edge e a b))
    (x : Fin n→Bool) (z : (Fin N.shape.edges×Bool)→Bool) :
    N.assignmentTerm (F.flip x) (F.flip z)=σ (N.assignmentTerm x z) := by
  unfold Network.assignmentTerm
  rw [map_mul,map_prod,map_prod]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    rw [F.assignment_flip]
    exact hv v _
  · apply Finset.prod_congr rfl
    intro e _
    exact he e _ _

/-- The complete finite weighted sum, using an explicit bijection rather than
an assertion about a graphical picture. -/
theorem denote_reversal (σ : K →+* K) {n : ℕ} (N : Network K n)
    (hv : ∀v,Reversal σ (N.vertex v))
    (he : ∀e a b,N.edge e (!a) (!b)=σ (N.edge e a b)) :
    Reversal σ N.denote := by
  intro x
  change (∑z : (Fin N.shape.edges×Bool)→Bool,N.assignmentTerm (F.flip x) z)=
    σ (∑z : (Fin N.shape.edges×Bool)→Bool,N.assignmentTerm x z)
  rw [map_sum]
  apply Fintype.sum_equiv (F.flipEquiv (Fin N.shape.edges×Bool))
  intro z
  change N.assignmentTerm (F.flip x) z=σ (N.assignmentTerm x (F.flip z))
  simpa only [F.flip_flip] using term_reversal σ N hv he x (F.flip z)

theorem nativeX_reversal (σ : K →+* K) (a b : Bool) :
    (Signature.disequality (!a) (!b) : K)=σ (Signature.disequality a b) := by
  cases a <;> cases b <;> simp [Signature.disequality]

/-- A nonzero projective directed pin is impossible whenever the coefficient
map is injective. This allows any complex scaling of the proposed pin. -/
theorem no_projective_pin (σ : K →+* K) (hinj : Function.Injective σ)
    {f : Signature K 2} (hf : Reversal σ f) (c : K) (hc : c≠0) :
    f≠c • F.oriented01 := by
  intro h
  have hs := hf ![false,true]
  rw [h] at hs
  have hz : (0 : K)=σ c := by
    simpa [F.oriented01,F.flip,Pi.smul_apply,smul_eq_mul] using hs
  apply hc
  apply hinj
  simpa only [map_zero] using hz.symm

abbrev ConjugateReversal {n : ℕ} (f : Signature ℂ n) : Prop :=
  Reversal Complex.conjAe.toRingHom f

theorem complex_network {n : ℕ} (N : Network ℂ n)
    (hv : ∀v,ConjugateReversal (N.vertex v))
    (he : ∀e,N.edge e=Signature.disequality) : ConjugateReversal N.denote := by
  apply denote_reversal
  · exact hv
  · intro e a b
    rw [he e]
    exact nativeX_reversal _ a b

theorem complex_no_projective_pin (N : Network ℂ 2)
    (hv : ∀v,ConjugateReversal (N.vertex v))
    (he : ∀e,N.edge e=Signature.disequality) (c : ℂ) (hc : c≠0) :
    N.denote≠c • F.oriented01 :=
  no_projective_pin Complex.conjAe.toRingHom Complex.conjAe.injective
    (complex_network N hv he) c hc

open Holant.LocalDrafts.Hardness.EightVertexNonexception

/-- Every original one-copy cap has conjugate weights. Thus this whole complex
symmetry class evades both direct cancellation and unequal-norm cap access. -/
theorem cap_conjugate (M : Signature ℂ 4) (h : ConjugateReversal M) (i : Fin 6) :
    (GeneralCancellationCapPin.coefficients M i).2=
      star ((GeneralCancellationCapPin.coefficients M i).1) := by
  have hb := h ![false,false,true,true]
  have hc := h ![false,true,false,true]
  have hd := h ![false,true,true,false]
  have hy : (entries M).y=star ((entries M).b) := by
    change M _=star (M _ )
    calc
      _ = M (F.flip ![false,false,true,true]) := by
        apply congrArg M; funext k; fin_cases k <;> rfl
      _ = _ := hb
  have hz : (entries M).z=star ((entries M).c) := by
    change M _=star (M _ )
    calc
      _ = M (F.flip ![false,true,false,true]) := by
        apply congrArg M; funext k; fin_cases k <;> rfl
      _ = _ := hc
  have hw : (entries M).w=star ((entries M).d) := by
    change M _=star (M _ )
    calc
      _ = M (F.flip ![false,true,true,false]) := by
        apply congrArg M; funext k; fin_cases k <;> rfl
      _ = _ := hd
  fin_cases i <;> simp [GeneralCancellationCapPin.coefficients,hy,hz,hw,add_comm]

theorem cap_norm_equal (M : Signature ℂ 4) (h : ConjugateReversal M) (i : Fin 6) :
    ‖(GeneralCancellationCapPin.coefficients M i).1‖=
      ‖(GeneralCancellationCapPin.coefficients M i).2‖ := by
  rw [cap_conjugate M h i,norm_star]

theorem no_geometric_cap (M : Signature ℂ 4) (h : ConjugateReversal M) :
    ¬GeneralGeometricCapLocal.Applicable M := by
  rintro ⟨⟨i,b⟩,hp,hq,hn⟩
  have he := cap_norm_equal M h i
  cases b
  · exact hn (by simpa [GeneralCancellationCapPin.oriented] using he)
  · exact hn (by simpa [GeneralCancellationCapPin.oriented] using he.symm)

theorem no_direct_cap (M : Signature ℂ 4) (h : ConjugateReversal M) :
    ¬GeneralCancellationCapPin.Applicable M := by
  rintro ⟨⟨i,b⟩,hp,hq⟩
  have he := cap_conjugate M h i
  cases b
  · change (GeneralCancellationCapPin.coefficients M i).1≠0 at hp
    change (GeneralCancellationCapPin.coefficients M i).2=0 at hq
    rw [he] at hq
    exact hp (star_eq_zero.mp hq)
  · change (GeneralCancellationCapPin.coefficients M i).2≠0 at hp
    change (GeneralCancellationCapPin.coefficients M i).1=0 at hq
    exact hp (by rw [he,hq,star_zero])

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConjugatePinObstruction
