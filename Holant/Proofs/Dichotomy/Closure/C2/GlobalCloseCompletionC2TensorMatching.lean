import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2MatchingLines
import Holant.Pauli.ExoticKlein.SixPortModel

/-! Pure literal C2 matching tensors and their exact coordinate symmetries.
The symmetry operations below are analytic equalities used for classification;
they do not declare any uncharged physical source resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2TensorMatching
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Pauli.ExoticKlein.SixPort
open GlobalCloseCompletionC2SixPortProblem (cardSupport)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K I J : Type*} [Field K]

def LiteralMatching (f : Tensor K I) : Prop := f = 0 ∨
  ∃ k : ℕ, ∃ ports : (Fin k × Bool) ≃ I, ∃ label : Fin k → Bool,
  ∃ c : K, c ≠ 0 ∧ f = productValue ports (fun i => originalC2Binary (label i)) c

def translate (mask : I → Bool) (f : Tensor K I) : Tensor K I :=
  fun w => f (fun i => w i ^^ mask i)

omit [Field K] in
theorem translate_involutive (mask : I → Bool) (f : Tensor K I) :
    translate mask (translate mask f) = f := by
  funext w
  apply congrArg f
  funext i
  change ((w i ^^ mask i) ^^ mask i) = w i
  cases w i <;> cases mask i <;> rfl

theorem binary_translate (p a b u v : Bool) :
    originalC2Binary (L := K) p (a ^^ u) (b ^^ v) =
      originalC2Binary ((p ^^ u) ^^ v) a b := by
  cases p <;> cases a <;> cases b <;> cases u <;> cases v <;>
    simp [originalC2Binary,X,Matrix.one_apply,Signature.disequality]

theorem translate_product {k : ℕ} (ports : (Fin k × Bool) ≃ I) (label : Fin k → Bool)
    (c : K) (mask : I → Bool) :
    translate mask (productValue ports (fun i => originalC2Binary (label i)) c) =
      productValue ports (fun i => originalC2Binary
        ((label i ^^ mask (ports (i,false))) ^^ mask (ports (i,true)))) c := by
  funext w
  simp only [translate,productValue,binary_translate]

theorem LiteralMatching.shift {f : Tensor K I} (h : LiteralMatching f) (mask : I → Bool) :
    LiteralMatching (translate mask f) := by
  rcases h with rfl | ⟨k,ports,label,c,hc,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k,ports,fun i => (label i ^^ mask (ports (i,false))) ^^ mask (ports (i,true)),
      c,hc,translate_product ports label c mask⟩

theorem LiteralMatching.of_translate {f : Tensor K I} (mask : I → Bool)
    (h : LiteralMatching (translate mask f)) : LiteralMatching f := by
  have hh := h.shift mask
  rwa [translate_involutive] at hh

theorem LiteralMatching.reindex {f : Tensor K I} (h : LiteralMatching f) (e : I ≃ J) :
    LiteralMatching (Tensor.reindex e f) := by
  rcases h with rfl | ⟨k,ports,label,c,hc,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k,ports.trans e,label,c,hc,rfl⟩

theorem LiteralMatching.of_reindex {f : Tensor K I} (e : I ≃ J)
    (h : LiteralMatching (Tensor.reindex e f)) : LiteralMatching f := by
  have hh := h.reindex e.symm
  have he : Tensor.reindex e.symm (Tensor.reindex e f) = f := by
    funext w
    simp only [Tensor.reindex,Equiv.symm_apply_apply]
  rwa [he] at hh

theorem literal_four_line (f : Signature K 4) (h : LiteralMatching f) :
    ∃ j : Fin 12, ∃ c : K, ∀ w : Fin 16,
      f ((wordEquiv 4).symm w) = c * (if w ∈ cardSupport j then 1 else 0) := by
  rcases h with rfl | ⟨k,ports,p,c,_hc,equation⟩
  · exact ⟨0,0,by intro w; simp⟩
  · have size := Fintype.card_congr ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at size
    have hk : k = 2 := by omega
    subst k
    obtain ⟨j,shape⟩ := GlobalCloseCompletionC2MatchingLines.four_port_lines ports ports.bijective p
    refine ⟨j,c,?_⟩
    intro w
    rw [equation]
    simp only [productValue,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
      GlobalCloseCompletionC2MatchingLines.binary_value]
    simp only [←shape w]
    split_ifs <;> simp_all

theorem of_current [NumberField K] (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion) = 2)
    (f : Tensor K I) (matching : MatchingOrZero (actualTransfers F) f) : LiteralMatching f := by
  by_cases zero : f=0
  · exact Or.inl zero
  · exact Or.inr (GlobalCloseCompletionC2MatchingLines.matching_literal F torsion hI cardTwo f zero matching)

theorem map_c2_binary {L : Type*} [Field L] (phi : K →+* L) (p a b : Bool) :
    phi (originalC2Binary p a b) = originalC2Binary p a b := by
  cases p <;> cases a <;> cases b <;> simp [originalC2Binary,X,Signature.disequality]

theorem LiteralMatching.map {L : Type*} [Field L] (phi : K →+* L)
    {f : Tensor K I} (h : LiteralMatching f) : LiteralMatching (fun w => phi (f w)) := by
  rcases h with rfl | ⟨k,ports,label,c,hc,rfl⟩
  · left
    funext w
    exact map_zero phi
  · refine Or.inr ⟨k,ports,label,phi c,(map_ne_zero phi).mpr hc,?_⟩
    funext w
    simp only [productValue,map_mul,map_prod,map_c2_binary]

private theorem c2_is_E (p a b : Bool) : originalC2Binary (L := ℂ) p a b =
    Holant.Pauli.ExoticKlein.E (if p then Holant.Pauli.ExoticKlein.xLabel else 0) a b := by
  cases p <;> cases a <;> cases b <;> rfl

theorem literal_six_product (f : Signature ℂ 6) (nonzero : f≠0)
    (matching : LiteralMatching f) : IsProduct f := by
  obtain ⟨k,ports,p,c,hc,equation⟩ := matching.resolve_left nonzero
  have size := Fintype.card_congr ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at size
  have hk : k=3 := by omega
  subst k
  refine ⟨⟨ports⟩,fun i => if p i then Holant.Pauli.ExoticKlein.xLabel else 0,c,hc,?_⟩
  rw [equation]
  funext w
  simp only [productValue,Holant.Pauli.ExoticKlein.Matching.tensor]
  apply congrArg (c * ·)
  apply Finset.prod_congr rfl
  intro i _hi
  exact c2_is_E (p i) _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2TensorMatching
end
