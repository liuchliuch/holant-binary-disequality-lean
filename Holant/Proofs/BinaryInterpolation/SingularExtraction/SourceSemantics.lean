import Holant.Proofs.BinaryInterpolation.SingularExtraction.QuerySize
import Holant.Proofs.BinaryInterpolation.SingularExtraction.ResidueMachine


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant Holant.Tractable Holant.Complexity
open OriginalQuery ResidueAnchors

variable {s : ℕ} {arity : ℕ → ℕ}

/-- No factor-extraction theorem occurs in this source boundary. The emitted
query and its normalization are the explicit constructions from this folder.
The dead case is a proved zero, and the live case permits zero oracle values. -/
theorem source_query_semantics
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (hs : ¬ Holant.Tractable.CommonOneSided
      (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex))))
    (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
    (hB : Gadget.Realizes (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex)))
      .disequality (outerSignature u v)) :
    ∃ U : PowerMacro G u, ∃ V : PowerMacro G v,
      ∀ r : UnaryInput (s:=s) (arity:=arity),
        value (Tables.familyTable G u v) r = 0 ∨
        ∃ q : Input s 1 arity,
          q.val = emitted G u v U V r ∧
          normalization G u v U V r ≠ 0 ∧
          (q.val.realize q.property G (fun _ => Signature.disequality)).denote Fin.elim0 /
            normalization G u v U V r = value (Tables.familyTable G u v) r := by
  obtain ⟨U, V⟩ := Classical.choice (source_labelled_powers G hs u v hu hv hB)
  refine ⟨U, V, ?_⟩
  intro r
  by_cases h : IsLive G u v U V r
  · exact Or.inr ⟨⟨emitted G u v U V r, emitted_valid G u v U V r h⟩,
      rfl, normalization_nonzero G u v U V r h, OriginalQuery.recover G u v U V r h⟩
  · exact Or.inl (OriginalQuery.dead G u v U V r h)

/-- The semantic source in the preceding theorem is exactly a decoded closed
network with the typed original-plus-unaries table, not a new sum convention. -/
theorem source_value_exact
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (u v : Bool → AlgebraicComplex) (r : UnaryInput (s:=s) (arity:=arity)) :
    value (Tables.familyTable G u v) r =
      (r.val.realize r.property
        (Tables.typed (Tables.familyTable G u v) (s+2) (Tables.adjoinedArity s arity 1 1))
        (fun _ => Signature.disequality)).denote Fin.elim0 :=
  (Tables.denote_eq_evaluate (Tables.familyTable G u v) r.val r.property).symm

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
