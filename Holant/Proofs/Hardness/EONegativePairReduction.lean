import Holant.Proofs.Hardness.EONegativeWitness
import Holant.Proofs.Hardness.EONegativeSubfamily

/-! A failed finite preprocessed EO criterion selects at most two actual
original labels and installs their literal one-query reduction to the original
family. Zero/nullary input labels may remain in the original dictionary, but
are never selected. No hardness of the resulting pair is presumed: that is
the remaining structural obligation of the universal negative theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativePairReduction
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
namespace W
export EONegativeWitness (Obstruction exists_pair pair_not_tract)
end W
namespace S
export EONegativeSubfamily (selected selectedArity label query controlled sourceEncoding targetEncoding Input
  query_rows query_edges query_ports query_vertices_length answer_recovers recovered_bytes)
end S
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def signature (i : Fin s) : AnySignature AlgebraicComplex := ⟨a i.val, G i⟩
def family : SignatureFamily AlgebraicComplex := Set.range (signature G)
def Kept (i : Fin s) : Prop := 0 < a i.val ∧ G i ≠ 0

/-- Selection is fixed finite preprocessing of the signature family, not a
runtime search over graph instances. Labels may coincide. -/
structure Selection where
  first : Fin s
  second : Fin s
  first_kept : Kept G first
  second_kept : Kept G second
  obstruction : W.Obstruction (signature G first) (signature G second)

variable (heo : ∀ g ∈ preprocess (family G), IsEO g)
variable (hbad : ¬EOTract (preprocess (family G)))

include heo hbad in
theorem selection_exists : Nonempty (Selection G) := by
  have hfin : (preprocess (family G)).Finite :=
    (Set.finite_range (signature G)).subset (fun _ h => h.1)
  obtain ⟨g, hg, h, hh, ho⟩ := W.exists_pair hfin heo hbad
  obtain ⟨⟨i, rfl⟩, hi⟩ := hg
  obtain ⟨⟨j, rfl⟩, hj⟩ := hh
  exact ⟨⟨i, j, hi, hj, ho⟩⟩

def choose : Selection G := Classical.choice (selection_exists G heo hbad)

variable (p : Selection G)

/-- Total raw label writer: zero maps to first, one maps to second. -/
def indices (k : ℕ) : ℕ := if k = 0 then p.first.val else p.second.val

theorem bounded (i : Fin 2) : indices G p i.val < s := by
  unfold indices
  split <;> first | exact p.first.isLt | exact p.second.isLt

def pair : (i : Fin 2) → Signature AlgebraicComplex (S.selectedArity (a:=a) (indices G p) i.val) :=
  S.selected G (indices G p) (bounded G p)

@[simp] theorem pair_zero :
    (⟨a (indices G p 0), pair G p 0⟩ : AnySignature AlgebraicComplex) = signature G p.first := rfl

@[simp] theorem pair_one :
    (⟨a (indices G p 1), pair G p 1⟩ : AnySignature AlgebraicComplex) = signature G p.second := rfl

theorem pair_family : family (pair G p) = {signature G p.first, signature G p.second} := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · intro hf
    rcases Set.mem_insert_iff.mp hf with hf | hf
    · exact ⟨0, (pair_zero G p).trans hf.symm⟩
    · exact ⟨1, (pair_one G p).trans (Set.mem_singleton_iff.mp hf).symm⟩

theorem pair_preprocessed : Preprocessed (family (pair G p)) := by
  rw [pair_family]
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact p.first_kept
  · rw [Set.mem_singleton_iff.mp hf]
    exact p.second_kept

theorem pair_negative : ¬EOTract (preprocess (family (pair G p))) := by
  rw [preprocess_eq_self (pair_preprocessed G p), pair_family]
  exact W.pair_not_tract p.obstruction

include heo in
theorem pair_eo : ∀ g ∈ family (pair G p), IsEO g := by
  rw [pair_family]
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact heo _ ⟨⟨p.first, rfl⟩, p.first_kept⟩
  · rw [Set.mem_singleton_iff.mp hf]
    exact heo _ ⟨⟨p.second, rfl⟩, p.second_kept⟩

/-- Actual original-field, count-preserving, bounded query reduction for the
selected obstructing pair. Only the original EO failure is used to select it. -/
def selectedControlled : LengthControlledOracleReduction
    (S.sourceEncoding (m:=2) (a:=a) (indices G (choose G heo hbad)))
    (O.originalPresentation (pair G (choose G heo hbad))).encoding
    (S.targetEncoding (s:=s) (a:=a)) (O.originalPresentation G).encoding
    (O.originalValue (pair G (choose G heo hbad))) (O.originalValue G) :=
  S.controlled G (indices G (choose G heo hbad)) (bounded G (choose G heo hbad))

/-- The graph writer sends every input occurrence to its chosen original
index. It preserves repeated occurrences, loops, parallel edges, and port order. -/
theorem selected_rows (r : S.Input (m:=2) (a:=a) (indices G (choose G heo hbad))) :
    (S.query (a:=a) (indices G (choose G heo hbad)) (bounded G (choose G heo hbad)) r).val.vertices =
      r.val.vertices.map (fun v => (if v.1=0 then (choose G heo hbad).first.val
        else (choose G heo hbad).second.val, v.2)) :=
  S.query_rows _ _ r

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (S.targetEncoding (s:=s) (a:=a)) (O.originalPresentation G).encoding
      (O.originalValue G) oracle)
    (r : S.Input (m:=2) (a:=a) (indices G (choose G heo hbad))) :=
  (selectedControlled G heo hbad).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativePairReduction
