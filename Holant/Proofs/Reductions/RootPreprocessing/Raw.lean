import Holant.Proofs.Reductions.RootPreprocessing.Retained


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
open Holant.Algebraic Holant.Complexity RawClosedNetwork
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def keepNat (i : ℕ) : Prop := ∃ hi : i < s, Keep G ⟨i,hi⟩
def compactNat (i : ℕ) : ℕ :=
  if hi : i < s then if hk : Keep G ⟨i,hi⟩ then (compact G ⟨i,hi⟩ hk).val else 0 else 0
@[simp] theorem keepNat_fin (i : Fin s) : keepNat G i.val ↔ Keep G i := by
  simp [keepNat,i.isLt]
@[simp] theorem compactNat_fin (i : Fin s) (hi : Keep G i) :
    compactNat G i.val = (compact G i hi).val := by simp [compactNat,i.isLt,hi]

def deadWeight (i : ℕ) : ℕ := if hi : i < s then if G ⟨i,hi⟩ = 0 then 1 else 0 else 0
def zeroCount (r : RawClosedNetwork) : ℕ := (r.vertices.map (fun row => deadWeight G row.1)).sum
def Clean (r : RawClosedNetwork) : Prop := zeroCount G r = 0

theorem clean_iff (r : Input (s:=s) (a:=a)) :
    Clean G r.val ↔ ∀ row ∈ r.val.vertices, ∀ hi : row.1 < s, G ⟨row.1,hi⟩ ≠ 0 := by
  have hv := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  change (r.val.vertices.map (fun row => deadWeight G row.1)).sum = 0 ↔ _
  rw [List.sum_eq_zero_iff_forall_eq_nat]
  constructor
  · intro h row hm hi hz
    have hw := h (deadWeight G row.1) (List.mem_map.mpr ⟨row,hm,rfl⟩)
    simpa [deadWeight,hi,hz] using hw
  · intro h z hz
    obtain ⟨row,hm,rfl⟩ := List.mem_map.mp hz
    simp [deadWeight,(hv.1 row hm).1,h row hm]

abbrev GoodInput := {r : Input (s:=s) (a:=a) // Clean G r.val}
def rowChunk (row : RawVertex) : List RawVertex :=
  if keepNat G row.1 then [(compactNat G row.1,row.2)] else []
def keptRows (rows : List RawVertex) : List RawVertex := rows.flatMap (rowChunk G)
def stripped (r : RawClosedNetwork) : RawClosedNetwork := ⟨keptRows G r.vertices,r.edges⟩

theorem discarded_ports (r : GoodInput G) (row : RawVertex) (hm : row ∈ r.val.val.vertices)
    (hk : ¬ keepNat G row.1) : row.2 = [] := by
  have hv := ((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.val.property).1 row hm
  have hn := (clean_iff G r.val).mp r.property row hm hv.1
  have ha : a row.1 = 0 := by
    by_contra hz
    exact hk ⟨hv.1,⟨Nat.pos_of_ne_zero hz,hn⟩⟩
  exact List.eq_nil_of_length_eq_zero (hv.2.trans ha)

theorem kept_endpoints (rows : List RawVertex)
    (h : ∀ row ∈ rows, ¬ keepNat G row.1 → row.2 = []) :
    ((keptRows G rows).map Prod.snd).flatten = (rows.map Prod.snd).flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases hk : keepNat G row.1
    · simpa [keptRows,rowChunk,hk] using congrArg (row.2 ++ ·) ht
    · simpa [keptRows,rowChunk,hk,h row (by simp) hk] using ht

theorem stripped_wellFormed (r : GoodInput G) :
    (stripped G r.val.val).WellFormed (count G) 1 (targetArity G) := by
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.val.property
  apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_,hr.2.1,?_⟩
  · intro q hq
    obtain ⟨row,hm,hq⟩ := List.mem_flatMap.mp hq
    by_cases hk : keepNat G row.1
    · have he : q = (compactNat G row.1,row.2) := by simpa [rowChunk,hk] using hq
      subst q
      obtain ⟨hi,hkeep⟩ := hk
      rw [compactNat_fin G ⟨row.1,hi⟩ hkeep]
      exact ⟨(compact G ⟨row.1,hi⟩ hkeep).isLt,by
        rw [target_arity,include_compact]
        exact (hr.1 row hm).2⟩
    · simp [rowChunk,hk] at hq
  · change ((keptRows G r.val.val.vertices).map Prod.snd).flatten.Perm _
    rw [kept_endpoints G _ (discarded_ports G r)]
    exact hr.2.2

abbrev TargetInput := ExactSignatureTables.Input (count G) 1 (targetArity G)
def cleanQuery (r : GoodInput G) : TargetInput G := ⟨stripped G r.val.val,stripped_wellFormed G r⟩
def emptyQuery : TargetInput G := ⟨⟨[],[]⟩,by
  simp [RawClosedNetwork.WellFormed,RawClosedNetwork.endpoints,RawClosedNetwork.expectedEndpoints]⟩
def select (r : Input (s:=s) (a:=a)) : Option (GoodInput G) :=
  if h : Clean G r.val then some ⟨r,h⟩ else none
def query (r : Input (s:=s) (a:=a)) : TargetInput G :=
  ((select G r).map (cleanQuery G)).getD (emptyQuery G)

@[simp] theorem query_clean (r : Input (s:=s) (a:=a)) (h : Clean G r.val) :
    query G r = cleanQuery G ⟨r,h⟩ := by simp [query,select,h]
@[simp] theorem query_zero (r : Input (s:=s) (a:=a)) (h : ¬ Clean G r.val) :
    query G r = emptyQuery G := by simp [query,select,h]
theorem clean_edges (r : GoodInput G) : (cleanQuery G r).val.edges = r.val.val.edges := rfl
theorem clean_endpoints (r : GoodInput G) :
    (cleanQuery G r).val.endpoints = r.val.val.endpoints :=
  kept_endpoints G _ (discarded_ports G r)

end Holant.LocalDrafts.Hardness.RootPreprocessing
