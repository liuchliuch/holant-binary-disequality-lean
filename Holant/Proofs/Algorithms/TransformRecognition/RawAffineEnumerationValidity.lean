import Holant.Proofs.Algorithms.TransformRecognition.RawAffineTemplateNormalization


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineEnumerationValidity
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver (mem_cross)
open RawAffineEnumeration

theorem vector_spec {A : Type} (alphabet : List A) (n : ℕ) (xs : List A)
    (hx : xs ∈ StructuralListMachine.exactLength alphabet n) :
    xs.length=n ∧ ∀ a ∈ xs, a ∈ alphabet := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  refine ⟨List.length_ofFn,?_⟩
  have hm : ∀ (k : ℕ) (v : Fin k → A), v ∈ FiniteBranchEnumeration.vectors alphabet k →
      ∀ i, v i ∈ alphabet := by
    intro k
    induction k with
    | zero => intro v hv i; exact Fin.elim0 i
    | succ k ih =>
      intro v hv
      obtain ⟨a,ha,hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hv
      intro i
      induction i using Fin.cases with
      | zero => exact ha
      | succ i => exact ih t ht i
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact hm n v hv i

theorem lists_spec {A : Type} (alphabet xs : List A) (h : ℕ)
    (hx : xs ∈ StructuredCatalogue.lists alphabet h) :
    xs.length ≤ h ∧ ∀ a ∈ xs, a ∈ alphabet := by
  obtain ⟨n,hn,hx⟩ := List.mem_flatMap.mp hx
  have hs := vector_spec alphabet n xs hx
  exact ⟨by have hn' := List.mem_range.mp hn; omega,hs.2⟩

theorem row_spec (n : ℕ) (r : EncodedTable.Row) (hr : r ∈ rows n) : r.2.length=n := by
  have hw := (mem_cross.mp hr).2
  exact (vector_spec [false,true] n r.2 hw).1

theorem bounded_get_mem {A : Type} (xs : List A) (fallback : A) (i : ℕ) (hi : i<xs.length) :
    xs.getD i fallback ∈ xs := by
  rw [List.getD_eq_getElem xs fallback hi]
  exact List.getElem_mem _

theorem generated_regular (n : ℕ) (d : EncodedTable.Data) (hd : d ∈ templates n) :
    d.1=n ∧ EncodedTable.Regular d := by
  obtain ⟨⟨support,phase⟩,hp,rfl⟩ := List.mem_map.mp hd
  obtain ⟨hs,hphase⟩ := mem_cross.mp hp
  obtain ⟨hc,hrest⟩ := mem_cross.mp hphase
  obtain ⟨hl,hm⟩ := mem_cross.mp hrest
  have hsupport := lists_spec (rows n) support (rows n).length hs
  have hlinear := vector_spec [0,1,2,3] n phase.2.1 hl
  have hmatrix := vector_spec (mixedRows n) n phase.2.2 hm
  refine ⟨rfl,?_,hlinear.1,hmatrix.1,?_,?_⟩
  · intro row hr
    exact row_spec n row (hsupport.2 row hr)
  · intro row hr
    exact (vector_spec [0,2] n row (hmatrix.2 row hr)).1
  · intro i j _
    let row := phase.2.2.getD i.val []
    have hir : i.val<phase.2.2.length := by rw [hmatrix.1]; exact i.isLt
    have hrow := vector_spec [0,2] n row (hmatrix.2 row (bounded_get_mem _ [] _ hir))
    have hjr : j.val<row.length := by rw [hrow.1]; exact j.isLt
    have hv := hrow.2 (row.getD j.val 0) (bounded_get_mem _ 0 _ hjr)
    simpa only [EncodedTable.mixed,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,row] using hv

/-- The generated candidate determines an actual paper normal form; the
emitted coefficient is unchanged by removal of duplicate support rows. -/
theorem generated_coefficient {v : ℕ} (imaginary : Fin v) (n : ℕ)
    (d : EncodedTable.Data) (hd : d ∈ templates n) (x : Fin d.1 → Bool) :
    RationalAffineTemplateMachine.value (v,imaginary.val,d,List.ofFn x) =
      Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.rowWire
        (SymbolicPhaseCoefficients.affineCoefficient imaginary
          (RawAffineTemplateNormalization.normalize d) x) :=
  RawAffineTemplateNormalization.coefficient_exact imaginary d (generated_regular n d hd).2 x

end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineEnumerationValidity
