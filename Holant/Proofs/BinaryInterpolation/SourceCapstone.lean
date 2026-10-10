import Holant.Proofs.BinaryInterpolation.FieldSource


namespace Holant.LocalDrafts.BinaryInterpolation.SourceCapstone
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀ i x, IsAlgebraic ℚ (G i x))

/-- Precisely the source-direct hypothesis; no B-membership or literal-I
resource is added. All witnesses are fixed independently of the graph input. -/
theorem binary_interpolation (B : Binary (K:=ℂ)) (hB : B ≠ 0)
    (hd : Matrix.det (B*X) ≠ 0) (hi : ¬ ProjectivelyFinite (B*X))
    (hreal : Gadget.Realizes
      (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature ℂ)))
      .disequality (Chains.binarySignature B)) :
    ∃ M : AlgebraicSource.Macro G B, ∃ p : AlgebraicSource.Pencil M.binary,
      p.H ≠ 0 ∧ p.H.rank = 1 ∧ AlgebraicSource.EntriesAlgebraic p.H ∧
      Nonempty (PolyTimeOracleReduction
        (FieldSource.inputEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
        (FieldSource.targetEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
        (AlgebraicSource.CommonField.sourceValue G M.binary p)
        (AlgebraicSource.CommonField.targetValue G M.binary p)) := by
  have hup : Gadget.RealizesUpTo
      (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature ℂ)))
      .disequality (Chains.binarySignature B) := by
    refine ⟨1,one_ne_zero,?_⟩
    simpa only [one_mul] using hreal
  obtain ⟨M⟩ := AlgebraicSource.exists_macro G halg B hB hd hi hup
  obtain ⟨p⟩ := M.pencil_exists
  exact ⟨M,p,p.H_nonzero,p.H_rank,p.H_algebraic,⟨FieldSource.reduction G halg M p⟩⟩

variable {B : Binary (K:=ℂ)} (M : AlgebraicSource.Macro G B)
variable (p : AlgebraicSource.Pencil M.binary)

def query (r : FieldSource.Input (s:=s) (arity:=arity)) (i : Fin (occurrences s r.val+1)) :=
  Chains.Compiler.OriginalFamily.value arity M.label.template M.label.wellFormed rfl (0 : Fin 1)
    ⟨FieldSource.asMacroInput G M r,i⟩

/-- Literal original-family physical query counts, after the binary macro has
been eliminated, with the fixed macro's own vertex count as the constant. -/
theorem query_vertex_bound (r : FieldSource.Input (s:=s) (arity:=arity))
    (hm : 1 ≤ occurrences s r.val) (i : Fin (occurrences s r.val+1)) :
    (query G M r i).val.vertices.length-r.val.vertices.length ≤
      2*M.label.template.vertices.length*(occurrences s r.val)^2 :=
  EncodedBatch.quadratic_vertices arity M.label.template M.label.wellFormed rfl (0 : Fin 1)
    (FieldSource.asMacroInput G M r) hm i

theorem total_vertex_bound (r : FieldSource.Input (s:=s) (arity:=arity))
    (hm : 1 ≤ occurrences s r.val) :
    (∑ i : Fin (occurrences s r.val+1),
      ((query G M r i).val.vertices.length-r.val.vertices.length)) ≤
      4*M.label.template.vertices.length*(occurrences s r.val)^3 :=
  EncodedBatch.cubic_vertices arity M.label.template M.label.wellFormed rfl (0 : Fin 1)
    (FieldSource.asMacroInput G M r) hm

/-- Every emitted query is in the original Γ input type; its encoded byte
length is polynomial in the original Γ∪{H} input length. -/
theorem query_bytes (r : FieldSource.Input (s:=s) (arity:=arity))
    (i : Fin (occurrences s r.val+1)) :
    ((FieldSource.targetEncoding (s:=s) (arity:=arity)).encode (query G M r i)).length ≤
      (EncodedBatch.queriesComputes arity M.label.template M.label.wellFormed rfl (0 : Fin 1)).outputBound.bound.eval
        ((FieldSource.inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  let qs := EncodedBatch.queries arity M.label.template M.label.wellFormed rfl (0 : Fin 1)
    (FieldSource.asMacroInput G M r)
  have hmem : query G M r i ∈ qs := by
    exact List.mem_map.mpr ⟨i,by simp,rfl⟩
  have h := OracleBatch.member_length_le
    (qs.map (FieldSource.targetEncoding (s:=s) (arity:=arity)).encode)
    ((FieldSource.targetEncoding (s:=s) (arity:=arity)).encode (query G M r i))
    (List.mem_map.mpr ⟨query G M r i,hmem,rfl⟩)
  have hs := (EncodedBatch.queriesComputes arity M.label.template M.label.wellFormed rfl
    (0 : Fin 1)).outputBound.length_le (FieldSource.asMacroInput G M r)
  rw [OracleBatch.list_encode] at hs
  exact h.trans hs

/-- The exact ambient signature family and value are unchanged by the chosen
faithful field. In particular H is added to the original Γ, not to a virtual
family containing a new B or identity signature. -/
theorem source_family :
    Set.range (fun i : Fin (s+1) =>
      (⟨UniversalPairReduction.extendedArity s arity i.val,
        UniversalPairReduction.BinaryFamily.signatures G p.H i⟩ : AnySignature ℂ)) =
    Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature ℂ)) ∪
      {(⟨2,Chains.binarySignature p.H⟩ : AnySignature ℂ)} :=
  AlgebraicSource.CommonField.source_family_exact G M.binary p

end
end Holant.LocalDrafts.BinaryInterpolation.SourceCapstone
