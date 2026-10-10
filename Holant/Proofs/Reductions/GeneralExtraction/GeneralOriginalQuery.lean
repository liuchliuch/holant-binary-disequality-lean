import Holant.Proofs.BinaryInterpolation.SingularExtraction.OriginalQuery
import Holant.Proofs.Reductions.GeneralExtraction.GeneralPowerExposure
import Holant.Proofs.Reductions.GeneralExtraction.GeneralResidueQuery
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.Complexity.FixedGadgetSubstitution.Identity


noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalQuery
open scoped BigOperators
open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralPowerExposure RawFactorGrouping
variable {K : Type} [Field K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val)) (f : Signature K (arity s))
variable (P : PowerMacro G f)

abbrev Input := ResidueAnchors.Input (s+1) 1 arity
abbrev factorTable := sourceTable (Choice.table G) s f
abbrev powerTable := targetTable (Choice.table G) s P.exponent f

theorem source_old (i : Fin s) :
    Tables.typed (factorTable G f) (s+1) arity ⟨i.val, by omega⟩ = G i := by
  funext x
  simp [Tables.typed, factorTable, sourceTable, Choice.table, i.isLt,
    Nat.ne_of_lt i.isLt, List.getD_eq_getElem]

theorem source_new :
    Tables.typed (factorTable G f) (s+1) arity ⟨s, by omega⟩ = f := by
  funext x
  simp [Tables.typed, factorTable, sourceTable, GroupedWords.word, List.getD_eq_getElem]

/-- The source really adds f itself; the tensor power occurs only in an
intermediate query and is not substituted for the claimed source family. -/
theorem source_family_exact :
    Set.range (fun i : Fin (s+1) => (⟨arity i.val,
      Tables.typed (factorTable G f) (s+1) arity i⟩ : AnySignature K)) =
      Set.range (fun i : Fin s => (⟨arity i.val, G i⟩ : AnySignature K)) ∪ {⟨arity s, f⟩} := by
  ext h
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val < s
    · exact Or.inl ⟨⟨i.val, hi⟩, congrArg (fun t : Signature K (arity i.val) => (⟨arity i.val,t⟩ : AnySignature K))
        (source_old G f ⟨i.val,hi⟩).symm⟩
    · have he : i = ⟨s, by omega⟩ := Fin.ext (by change i.val = s; omega)
      rw [he]
      exact Or.inr (by simp only [Set.mem_singleton_iff, source_new])
  · rintro (⟨i, rfl⟩ | hh)
    · exact ⟨⟨i.val, by omega⟩, by dsimp only; rw [source_old]⟩
    · rw [Set.mem_singleton_iff] at hh
      subst h
      exact ⟨⟨s, by omega⟩, by dsimp only; rw [source_new]⟩

def templates (i : ℕ) : Template :=
  if i = s then P.labels.template else identityTemplate arity i

theorem templates_valid : ∀ i < s+1, (templates G f P i).WellFormed s 1 arity := by
  intro i hi
  by_cases he : i = s
  · simpa [templates, he] using P.labels.wellFormed
  · have his : i < s := by omega
    simpa [templates, he] using identityTemplate_wellFormed (b:=1) arity ⟨i, his⟩

theorem sourceArity_eq : sourceArity (templates G f P) =
    RawGrouping.changedArity arity s (P.exponent * arity s) := by
  funext i
  by_cases he : i = s <;>
    simp [sourceArity, templates, RawGrouping.changedArity, he, identityTemplate]

def source : (i : Fin (s+1)) → Signature K (sourceArity (templates G f P) i.val) :=
  Tables.typed (powerTable G f P) (s+1) (sourceArity (templates G f P))

def scales (i : Fin (s+1)) : K := if i.val = s then P.scale else 1

theorem local_value (i : Fin (s+1)) :
    ((templates G f P i.val).network (templates_valid G f P i.val i.isLt)
      G (fun _ => Signature.disequality)).denote = scales G f P i • source G f P i := by
  change ((templates G f P i.val).network _ G (fun _ => Signature.disequality)).denote =
    fun x => scales G f P i * powerTable G f P i.val (List.ofFn x)
  rcases i with ⟨i, hi⟩
  by_cases he : i = s
  · subst i
    refine OriginalQuery.network_value_of_eq G (templates G f P s) P.labels.template _ P.labels.wellFormed
      (by simp [templates]) (fun bits => scales G f P ⟨s,hi⟩ * powerTable G f P s bits) ?_
    rw [P.value]
    funext x
    simp [scales, powerTable, targetTable, GroupedWords.power_eq_blockPower, List.getD_eq_getElem]
  · have his : i < s := by omega
    refine OriginalQuery.network_value_of_eq G (templates G f P i) (identityTemplate arity i) _
      (identityTemplate_wellFormed arity ⟨i,his⟩) (by simp [templates,he])
      (fun bits => scales G f P ⟨i,hi⟩ * powerTable G f P i bits) ?_
    rw [identityTemplate_denote arity ⟨i,his⟩ G (fun _ => Signature.disequality)]
    funext x
    simp [scales,powerTable,targetTable,he,Choice.table,his,List.getD_eq_getElem,identityTemplate]

theorem physical_value (r : RawClosedNetwork)
    (hr : r.WellFormed (s+1) 1 (sourceArity (templates G f P))) :
    ((replace (templates G f P) r).realize
      (FixedGadgetSubstitution.query_wellFormed (templates G f P) r hr (templates_valid G f P))
      G (fun _ => Signature.disequality)).denote Fin.elim0 =
        P.scale ^ occurrences s r * Choice.evaluate (powerTable G f P) r.edges.length r.vertices := by
  rw [replacement_partition (templates G f P) r hr (templates_valid G f P)
    (source G f P) G (fun _ => Signature.disequality) (scales G f P) (local_value G f P)]
  have hs : (∏ j, scales G f P (r.signatureLabel hr j)) = P.scale ^ occurrences s r := by
    unfold scales
    exact scale_product s P.scale r
  rw [hs]
  congr 1
  exact Tables.denote_eq_evaluate (powerTable G f P) r hr

abbrev IsLive (r : Input (s:=s) (arity:=arity)) :=
  GeneralResidueQuery.IsLive (Choice.table G) s P.exponent P.positive f r

def grouped (r : Input (s:=s) (arity:=arity)) (h : IsLive G f P r) : RawClosedNetwork :=
  (GeneralResidueQuery.query (Choice.table G) s P.exponent P.positive f (by omega) r h).val

theorem grouped_valid (r : Input (s:=s) (arity:=arity)) (h : IsLive G f P r) :
    (grouped G f P r h).WellFormed (s+1) 1 (sourceArity (templates G f P)) := by
  rw [sourceArity_eq]
  exact (GeneralResidueQuery.query (Choice.table G) s P.exponent P.positive f (by omega) r h).property

def emitted (r : Input (s:=s) (arity:=arity)) (h : IsLive G f P r) :
    ResidueAnchors.Input s 1 arity :=
  ⟨replace (templates G f P) (grouped G f P r h),
    FixedGadgetSubstitution.query_wellFormed (templates G f P) _
      (grouped_valid G f P r h) (templates_valid G f P)⟩

def normalization (r : Input (s:=s) (arity:=arity)) (h : IsLive G f P r) : K :=
  P.scale ^ occurrences s (grouped G f P r h) *
    GeneralResidueQuery.scale (Choice.table G) s P.exponent P.positive f r

theorem normalization_nonzero (r : Input (s:=s) (arity:=arity)) (h : IsLive G f P r) :
    normalization G f P r h ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ P.scale_ne_zero)
    (GeneralResidueQuery.scale_nonzero (Choice.table G) s P.exponent P.positive f r h)

def originalValue (r : ResidueAnchors.Input s 1 arity) : K :=
  (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0

theorem emitted_value (r : Input (s:=s) (arity:=arity)) (h : IsLive G f P r) :
    originalValue G (emitted G f P r h) =
      normalization G f P r h * ResidueAnchors.value (factorTable G f) r := by
  change ((replace _ _).realize _ _ _).denote _ = _
  rw [physical_value G f P _ (grouped_valid G f P r h)]
  have hv := GeneralResidueQuery.query_value (Choice.table G) s P.exponent P.positive f
    (by omega : s < s+1) r h
  change Choice.evaluate (powerTable G f P) (grouped G f P r h).edges.length
    (grouped G f P r h).vertices = _ at hv
  rw [hv]
  unfold normalization
  ring

theorem recover (r : Input (s:=s) (arity:=arity)) (h : IsLive G f P r) :
    originalValue G (emitted G f P r h) / normalization G f P r h =
      ResidueAnchors.value (factorTable G f) r := by
  rw [emitted_value]
  exact mul_div_cancel_left₀ _ (normalization_nonzero G f P r h)

def plan (r : Input (s:=s) (arity:=arity)) :
    GeneralResidueQuery.QueryPlan (ResidueAnchors.Input s 1 arity) K :=
  if h : IsLive G f P r then .one (emitted G f P r h) (normalization G f P r h)⁻¹ else .zero

theorem plan_correct (r : Input (s:=s) (arity:=arity)) :
    (plan G f P r).run (originalValue G) = ResidueAnchors.value (factorTable G f) r := by
  by_cases h : IsLive G f P r
  · simpa only [plan, dif_pos h, GeneralResidueQuery.QueryPlan.run, ← div_eq_mul_inv]
      using recover G f P r h
  · simp only [plan, dif_neg h, GeneralResidueQuery.QueryPlan.run]
    exact (ResidueAnchors.dead_value (factorTable G f) s s P.exponent 1 P.positive
      (by omega) r h).symm

/-- Family support alone constructs the required power macro. Thus the
all-input query above has no external cap/carrier/macro correctness premise.
It remains a graph-query result until the final finite-machine join exists. -/
theorem support_query (htwo : (2 : K) ≠ 0)
    (hF : GeneralCarrierExistence.MixedSupport
      (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature K))))
    {n : ℕ} (g : Signature K n) (hn : 0 < n) (hg : g ≠ 0)
    (hfg : (⟨arity s + n, Signature.tensor f g⟩ : AnySignature K) ∈
      Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature K))) :
    ∃ P : PowerMacro G f, ∀ r : Input (s:=s) (arity:=arity),
      (plan G f P r).run (originalValue G) = ResidueAnchors.value (factorTable G f) r := by
  obtain ⟨P⟩ := labelled_power G htwo hF f g hn hg hfg
  exact ⟨P, plan_correct G f P⟩

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalQuery
