import Holant.Complexity.BinaryInterpolation.Chains.Records

namespace Holant.Complexity.BinaryInterpolation.Chains
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

def appendRoute (e : ℕ) (p : Fin 2 ⊕ (Fin e × Bool)) : Fin 2 ⊕ (Fin (e + 1) × Bool) :=
  (Network.contractPorts (e + 0) 2)
    ((Equiv.sumCongr seriesOrder (Equiv.refl _))
      ((Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (finSumFinEquiv : (Fin e ⊕ Fin 0) ≃ Fin (e + 0)) (Equiv.refl Bool)))
          (Network.tensorPorts (Fin e) (Fin 0) 2 2 (.inl p))))

theorem appendRoute_embed (e : ℕ) (p : Fin 2 ⊕ (Fin e × Bool)) :
    Template.embed 2 (e + 1) (appendRoute e p) = extendEndpoint (Template.embed 2 e p) := by
  cases p with
  | inl i => fin_cases i <;> rfl
  | inr p => rfl

theorem compile_vertices_succ (label edge k : ℕ) :
    (compile label edge (k + 1)).vertices =
      (compile label edge k).vertices.map extendRow ++
        [(label, [.inr (0, true), .inl 1])] := by
  change (shapeTemplate (series (literal (K := ℚ) 0 k)
    (Network.corolla (binarySignature 0))).shape label edge).vertices = _
  simp only [shapeTemplate, series, Network.contract, reindex, tensor, enumerate,
    Network.tensorFinite, Network.corolla]
  rw [List.ofFn_add]
  simp only [List.ofFn_succ, List.ofFn_zero, List.map_ofFn, List.append_nil]
  congr 1
  · simp only [compile, shapeTemplate, List.map_ofFn, extendRow]
    apply congrArg List.ofFn
    funext v
    have hv : Fin.castLE (Nat.le_add_right (literal (K := ℚ) 0 k).shape.vertices 1) v =
        Fin.castAdd 1 v := rfl
    simp only [Equiv.trans_apply, Equiv.sigmaCongrLeft_apply, Fin.cast]
    generalize hq : finSumFinEquiv.symm
      (Fin.castLE (Nat.le_add_right (literal (K := ℚ) 0 k).shape.vertices 1) v) = q
    have hqv : q = Sum.inl v := by rw [←hq, hv]; exact finSumFinEquiv_symm_apply_castAdd v
    cases hqv
    change (label, List.ofFn _) = (label,
      (List.ofFn fun i : Fin ((literal (K := ℚ) 0 k).shape.arity v) =>
        Labelling.localEndpoint ((literal (K := ℚ) 0 k).shape.ports ⟨v,i⟩)).map extendEndpoint)
    rw [List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    change Template.embed 2 ((literal (K := ℚ) 0 k).shape.edges + 1)
      (appendRoute _ ((literal (K := ℚ) 0 k).shape.ports ⟨v,i⟩)) =
        extendEndpoint (Template.embed 2 _ ((literal (K := ℚ) 0 k).shape.ports ⟨v,i⟩))
    exact appendRoute_embed _ _
  · simp only [Equiv.trans_apply, Equiv.sigmaCongrLeft_apply, Fin.cast]
    generalize hq : finSumFinEquiv.symm
      (Fin.natAdd (literal (K := ℚ) 0 k).shape.vertices (0 : Fin 1)) = q
    have hqv : q = Sum.inr 0 := by rw [←hq]; exact finSumFinEquiv_symm_apply_natAdd 0
    cases hqv
    rfl

theorem compile_vertices_explicit (label edge k : ℕ) :
    (compile label edge k).vertices = (explicitTemplate label edge k).vertices := by
  induction k with
  | zero => rfl
  | succ k ih => rw [compile_vertices_succ,explicitTemplate_vertices_succ,ih]

/-- Exact equality of the executable closed-form records with the physical
positive-chain template, including every port occurrence and internal edge ID. -/
theorem compile_eq_explicitTemplate (label edge k : ℕ) :
    compile label edge k = explicitTemplate label edge k := by
  exact congrArg₂ (fun vs es => (⟨2,vs,es⟩ : Template))
    (compile_vertices_explicit label edge k)
    (by simp [compile,shapeTemplate,explicitTemplate])

theorem explicitTemplate_wellFormed {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b) (k : ℕ) :
    (explicitTemplate label.val edge.val k).WellFormed s b arity := by
  rw [←compile_eq_explicitTemplate]
  exact compile_wellFormed arity label hlabel edge k

theorem explicitTemplate_denote {K : Type*} [Field K] {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b) (k : ℕ)
    (B : Binary (K := K))
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K)
    (hB : (⟨arity label.val, signatures label⟩ : AnySignature K) =
      ⟨2, binarySignature B⟩) (hX : kernels edge = Signature.disequality) :
    ((explicitTemplate label.val edge.val k).network
      (explicitTemplate_wellFormed arity label hlabel edge k) signatures kernels).denote =
      binarySignature ((B * X) ^ (k + 1) * X) := by
  have he := template_denote_heq _ _ (explicitTemplate_wellFormed arity label hlabel edge k)
    (compile_wellFormed arity label hlabel edge k)
    (compile_eq_explicitTemplate label.val edge.val k).symm signatures kernels
  exact (eq_of_heq he).trans (compile_denote arity label hlabel edge k B signatures kernels hB hX)

theorem explicitTemplate_denote_scaled {K : Type*} [Field K] {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b) (k : ℕ)
    (B : Binary (K := K)) (c : K)
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K)
    (hB : (⟨arity label.val, signatures label⟩ : AnySignature K) =
      ⟨2, c • binarySignature B⟩) (hX : kernels edge = Signature.disequality) :
    ((explicitTemplate label.val edge.val k).network
      (explicitTemplate_wellFormed arity label hlabel edge k) signatures kernels).denote =
      c ^ (k + 1) • binarySignature ((B * X) ^ (k + 1) * X) := by
  rw [explicitTemplate_denote arity label hlabel edge k (c • B) signatures kernels hB hX,
    scaled_transfer_power,binarySignature_smul]

end Holant.Complexity.BinaryInterpolation.Chains
