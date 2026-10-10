import Holant.Proofs.Reductions.RootPreprocessing.ForestEndpoint


noncomputable section
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.Tractable
open RawClosedNetwork UniversalPairReduction.Surgery
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- The surviving rows retain both relative vertex order and each full port
list. In particular the two sides of a self-loop remain separate entries. -/
theorem keptRows_literal (rows : List RawVertex) : keptRows G rows =
    (rows.filter (fun row => decide (keepNat G row.1))).map
      (fun row => (compactNat G row.1,row.2)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [keptRows] at ih
    by_cases h : keepNat G row.1 <;> simp [keptRows,rowChunk,h,ih]

def emptyInput : Input (s:=s) (a:=a) := ⟨⟨[],[]⟩,by
  simp [RawClosedNetwork.WellFormed,endpoints,expectedEndpoints]⟩
@[simp] theorem empty_clean : Clean G (emptyInput (s:=s) (a:=a)).val := rfl
@[simp] theorem empty_query : query G (emptyInput (s:=s) (a:=a)) = emptyQuery G := by
  rw [query_clean G _ (empty_clean G)]
  apply Subtype.ext
  rfl
@[simp] theorem empty_context : context G (emptyInput (s:=s) (a:=a)) = 1 := by
  simp [context,scalar,OccurrenceProduct.value,emptyInput,Clean,zeroCount]
@[simp] theorem empty_value : sourceValue G (emptyInput (s:=s) (a:=a)) = 1 := by
  apply Subtype.ext
  rw [source_exact,query_value,empty_query,empty_target_value,empty_context]
  simp

theorem nullary_edges (r : Input (s:=s) (a:=a))
    (h : ∀ row ∈ r.val.vertices, a row.1 = 0) : r.val.edges = [] := by
  have hp : ∀ row ∈ r.val.vertices, row.2 = [] := by
    intro row hm
    have hr := ((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 row hm
    exact List.eq_nil_of_length_eq_zero (hr.2.trans (h row hm))
  have he : r.val.endpoints = [] := by
    change r.val.vertices.flatMap Prod.snd = []
    exact List.flatMap_eq_nil_iff.mpr hp
  have hn := r.property.2.2.length_eq
  rw [he,List.length_nil,expectedEndpoints_length] at hn
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem nullary_query (r : Input (s:=s) (a:=a))
    (h : ∀ row ∈ r.val.vertices, a row.1 = 0) : query G r = emptyQuery G := by
  by_cases hc : Clean G r.val
  · rw [query_clean G r hc]
    have hv : keptRows G r.val.vertices = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro row hm
      have hk : ¬ keepNat G row.1 := by
        rintro ⟨hi,hk⟩
        have hz := h row hm
        have hp := hk.1
        change 0<a row.1 at hp
        rw [hz] at hp
        exact Nat.not_lt_zero _ hp
      simp [rowChunk,hk]
    apply Subtype.ext
    change stripped G r.val = ⟨[],[]⟩
    simp [stripped,hv,nullary_edges r h]
  · exact query_zero G r hc

theorem nullary_value (r : Input (s:=s) (a:=a))
    (h : ∀ row ∈ r.val.vertices, a row.1 = 0) : sourceValue G r = context G r := by
  apply Subtype.ext
  rw [source_exact,query_value,nullary_query G r h,empty_target_value,mul_one]

/-- Repetition is occurrence-sensitive, including exponent zero. This product
is the same scalar specification computed by scalarComputes on actual input. -/
theorem repeated_scalar (i : Fin s) (h : a i.val = 0) (n : ℕ) :
    scalar G ⟨List.replicate n (i.val,[]),[]⟩ =
      (fieldCoefficient (sourceCoefficient G) (.inl ⟨i,fun _ => false⟩))^n := by
  simp [scalar,OccurrenceProduct.value,OccurrenceProduct.total,scalarLabel,i.isLt,h]

theorem zero_select (r : Input (s:=s) (a:=a)) (h : ¬ Clean G r.val) : select G r = none := by
  simp [select,h]

theorem scalar_transition_bound (r : Input (s:=s) (a:=a)) :
    ((scalarComputes G).outputs r).steps ≤
      (scalarComputes G).time.eval ((sourceEncoding (s:=s) (a:=a)).encode r).length :=
  ((scalarComputes G).outputs r).steps_le_m
theorem scalar_bit_bound (r : Input (s:=s) (a:=a)) :
    ((sourcePresentation G).encoding.encode (scalar G r.val)).length ≤
      (scalarComputes G).outputBound.bound.eval ((sourceEncoding (s:=s) (a:=a)).encode r).length :=
  (scalarComputes G).outputBound.length_le r
theorem scalar_primitive_bound (r : Input (s:=s) (a:=a)) :
    primitiveCost (scalarComputes G).machine ((scalarComputes G).outputs r).steps
      (some (Turing.initList (scalarComputes G).machine.computer
        ((sourceEncoding (s:=s) (a:=a)).encode r))) ≤
      (primitivePolynomial (scalarComputes G)).eval ((sourceEncoding (s:=s) (a:=a)).encode r).length :=
  computes_primitive_cost (scalarComputes G) r

end Holant.LocalDrafts.Hardness.RootPreprocessing
