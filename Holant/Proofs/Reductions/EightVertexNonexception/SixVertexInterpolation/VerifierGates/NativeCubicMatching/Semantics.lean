import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Literal
import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Source
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Holant
open Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
open WeightedMatchingInterpolation
namespace OldSource
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Occurrence
  (portWord support_iff bits list_product_indicator)
end OldSource
namespace Semantics
set_option backward.isDefEq.respectTransparency false

def word (g : UnitInput) (side : Bool) (r : ℕ) (c : Fin g.val.2.length → Bool) : List Bool :=
  (OldSource.portWord g side r c).map (fun b => if side then !b else b)
theorem word_normalized (g : UnitInput) (side : Bool) (r : ℕ) (c : Fin g.val.2.length → Bool) :
    normalizedWord side (word g side r c)=OldSource.portWord g side r c := by
  cases side <;> simp [word,normalizedWord,List.map_map,Function.comp_def]
theorem word_length (g : UnitInput) (side : Bool) (r : ℕ) (c : Fin g.val.2.length → Bool) :
    (word g side r c).length=(OldCompiler.ports g side r).length := by
  simp [word,OldSource.portWord]

def stagedPartition (g : UnitInput) : ℚ :=
  ∑ c : Fin g.val.2.length → Bool,
    ((OldCompiler.nodes g).map (fun p => Extensions.degreePartition p.1 (word g p.1 p.2 c))).prod

/-- The global 2^P is produced from actual node occurrences. The same
ordered matching support theorem supplies the count, not an input law. -/
theorem staged_exact (g : UnitInput) :
    stagedPartition g=(2 : ℚ)^(Incidence.paddingCount g)*unitValue g := by
  have hscale : ∀ xs : List (Bool × ℕ),
      (xs.map (fun p => (2 : ℚ)^(Extensions.padding (OldCompiler.ports g p.1 p.2).length))).prod=
        (2 : ℚ)^((xs.map (fun p => Extensions.padding (OldCompiler.ports g p.1 p.2).length)).sum) := by
    intro xs
    induction xs with
    | nil => simp
    | cons p xs ih => simp [ih,pow_add]
  have hweight (c : Fin g.val.2.length → Bool) :
      ((OldCompiler.nodes g).map (fun p => Extensions.degreePartition p.1 (word g p.1 p.2 c))).prod=
        (2 : ℚ)^(Incidence.paddingCount g)*
          (if OldIncidence.Selected g (OldSource.bits g c) then (1 : ℚ) else 0) := by
    simp_rw [Extensions.degree_exact,word_length]
    have hind (p : Bool × ℕ) : indicator p.1 (word g p.1 p.2 c)=
        if (OldSource.portWord g p.1 p.2 c).count true=1 then (1 : ℚ) else 0 := by
      unfold indicator
      rw [word_normalized]
    simp_rw [hind]
    rw [List.prod_map_mul,hscale]
    rw [OldSource.list_product_indicator]
    by_cases hs : OldIncidence.Selected g (OldSource.bits g c)
    · have ht := (OldSource.support_iff g c).mpr hs
      simp only [if_pos hs,if_pos ht]
      rfl
    · have ht : ¬(∀ p∈OldCompiler.nodes g,(OldSource.portWord g p.1 p.2 c).count true=1) :=
        fun h => hs ((OldSource.support_iff g c).mp h)
      simp only [if_neg hs,if_neg ht,mul_zero]
  unfold stagedPartition
  simp_rw [hweight]
  rw [←Finset.mul_sum]
  congr 1
  let e : (Fin g.val.2.length → Bool) ≃ OldIncidence.Selection g :=
    Equiv.arrowCongr (OldCompiler.occurrenceEquiv g) (Equiv.refl Bool)
  unfold unitValue
  rw [←OldIncidence.partition_count g]
  unfold Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Incidence.partition
  apply Fintype.sum_equiv e
  intro c
  rfl

theorem correction_exact (g : UnitInput) :
    stagedPartition g*((2 : ℚ)⁻¹)^(Incidence.paddingCount g)=unitValue g := by
  rw [staged_exact]
  exact Holant.Complexity.FixedFieldMachines.ScalarPower.cancel_scale_power 2 _ (by norm_num) _

/-- One bit per ACTUAL native-X edge, with the true-end complemented.
The equation is proved from the independent half-end sum, for loops too. -/
def nativeDenote {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature ℚ (s.arity v)) : Signature ℚ n :=
  fun x => ∑ a : Fin s.edges → Bool,
    ∏ v : Fin s.vertices,f v (s.assignment x (fun p => if p.2 then !a p.1 else a p.1) v)
theorem native_compression {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature ℚ (s.arity v)) :
    (Network.mk s f (fun _ => Signature.disequality)).denote=nativeDenote s f := by
  have hp (a b : Fin s.edges → Bool) :
      (∏ e : Fin s.edges,Signature.disequality (a e) (b e) : ℚ)=
        if b=(fun e => !a e) then 1 else 0 := by
    have he : (∀ e,a e≠b e) ↔ b=(fun e => !a e) := by
      constructor
      · intro h
        funext e
        have h' := h e
        cases ha : a e <;> cases hb : b e <;> simp_all
      · intro h e
        rw [h]
        change a e≠!a e
        cases a e <;> decide
    simp only [Signature.disequality,Fintype.prod_boole]
    by_cases ht : ∀ e,a e≠b e
    · rw [if_pos ht,if_pos (he.mp ht)]
    · have hn : ¬b=(fun e => !a e) := fun h => ht (he.mpr h)
      rw [if_neg ht,if_neg hn]
  funext x
  unfold Network.denote nativeDenote
  dsimp only
  rw [←(halfEdgeAssignmentsEquiv s.edges).symm.sum_comp,Fintype.sum_prod_type]
  simp only [halfEdgeAssignmentsEquiv,Equiv.coe_fn_symm_mk,Bool.false_eq_true,↓reduceIte,hp]
  simp

theorem raw_word (r : RawClosedNetwork) {s b : ℕ} {a : ℕ → ℕ}
    (hr : r.WellFormed s b a) (c : Fin r.edges.length → Bool) (v : Fin r.vertices.length) :
    List.ofFn ((r.shape hr).assignment Fin.elim0
      (fun p => if p.2 then !c p.1 else c p.1) v)=
        (r.vertices.get v).2.map (fun p =>
          if p.2 then !Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1
          else Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1) := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn,List.length_map,RawClosedNetwork.shape] using (hr.1 v).2.symm
  · intro i hi hj
    have hb : i<a (r.vertices.get v).1 := by simpa only [List.length_ofFn,RawClosedNetwork.shape] using hi
    have hport : i<(r.vertices.get v).2.length := by rw [(hr.1 v).2]; exact hb
    rw [List.getElem_ofFn,List.getElem_map]
    have he : (r.vertices.get v).2[i]=
        ((r.route hr ⟨v,⟨i,hb⟩⟩).1.val,(r.route hr ⟨v,⟨i,hb⟩⟩).2) := by
      rfl
    change (if (r.route hr ⟨v,⟨i,hb⟩⟩).2 then !c (r.route hr ⟨v,⟨i,hb⟩⟩).1
      else c (r.route hr ⟨v,⟨i,hb⟩⟩).1)=_
    rw [he,Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend_at]

theorem ports_side (g : UnitInput) (side : Bool) (r : ℕ) (p : RawEndpoint)
    (hp : p∈OldCompiler.ports g side r) : p.2=side := by
  unfold Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Compiler.ports at hp
  obtain ⟨j,_hj,hp⟩ := List.mem_flatMap.mp hp
  split_ifs at hp with h
  · exact congrArg Prod.snd (List.mem_singleton.mp hp)
  · simp at hp
theorem occurrence_word (g : UnitInput) (side : Bool) (r : ℕ) (c : Fin g.val.2.length → Bool) :
    (OldCompiler.ports g side r).map (fun p =>
      if p.2 then !Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1
      else Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1)=
        word g side r c := by
  unfold word OldSource.portWord
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  rw [ports_side g side r p hp]
  rfl

def sourceTensor (k : ℕ) : Signature ℚ (sourceArity Layout.templates k) :=
  fun x => Extensions.degreePartition (k%2==1) (List.ofFn x)
def virtualValue (g : UnitInput) : ℚ :=
  ((Layout.virtual g).realize (Layout.virtual_valid g) (fun i => sourceTensor i.val) edge).denote Fin.elim0
def targetEncoding := RawClosedNetwork.validatedEncoding 2 1 arity
abbrev TargetInput := {r : RawClosedNetwork // r.WellFormed 2 1 arity}
def targetValue (r : TargetInput) : ℚ := (r.val.realize r.property palette edge).denote Fin.elim0

theorem templates_denote (k : ℕ) :
    ((Layout.templates k).network (Layout.templates_valid k) palette edge).denote=sourceTensor k := by
  funext x
  change Fin (Layout.degree (k%2==1) (k/2)).boundary → Bool at x
  change ((Layout.degree (k%2==1) (k/2)).network (Layout.degree_valid _ _) palette edge).denote x=sourceTensor k x
  rw [Literal.degree_denote]
  unfold sourceTensor
  rw [Extensions.degree_exact]
  have hn : (List.ofFn x).length=k/2 := by simp [Layout.degree_boundary]
  simp only [Extensions.padding,hn]

theorem query_to_virtual (g : UnitInput) : targetValue (Layout.query g)=virtualValue g := by
  have h := replacement_partition Layout.templates (Layout.virtual g) (Layout.virtual_valid g)
    (fun k _ => Layout.templates_valid k) (fun i => sourceTensor i.val) palette edge
    (fun _ => (1 : ℚ)) (fun i => by simpa using templates_denote i.val)
  simpa [targetValue,Layout.query,Layout.raw,virtualValue] using h

theorem virtual_rows (g : UnitInput) : virtualValue g=
    ∑ c : Fin (Layout.virtual g).edges.length → Bool,
      ((Layout.virtual g).vertices.map (fun row => Extensions.degreePartition (row.1%2==1)
        (row.2.map (fun p =>
          if p.2 then !Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1
          else Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1)))).prod := by
  unfold virtualValue
  change (Network.mk ((Layout.virtual g).shape (Layout.virtual_valid g))
    (fun v => sourceTensor ((Layout.virtual g).signatureLabel (Layout.virtual_valid g) v).val)
    (fun _ => Signature.disequality)).denote Fin.elim0=_
  rw [native_compression]
  unfold nativeDenote
  apply Finset.sum_congr rfl
  intro c _
  change Fin (Layout.virtual g).edges.length → Bool at c
  rw [←List.ofFn_getElem_eq_map (Layout.virtual g).vertices (fun row =>
    Extensions.degreePartition (row.1%2==1) (row.2.map (fun p =>
      if p.2 then !Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1
      else Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c p.1))),
    List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  change Fin (Layout.virtual g).vertices.length at v
  exact congrArg (Extensions.degreePartition (((Layout.virtual g).vertices.get v).1%2==1))
    (raw_word (Layout.virtual g) (Layout.virtual_valid g) c v)

theorem virtual_staged (g : UnitInput) : virtualValue g=stagedPartition g := by
  rw [virtual_rows]
  unfold stagedPartition
  have he : (Layout.virtual g).edges.length=g.val.2.length := by simp [Layout.virtual]
  let e : (Fin (Layout.virtual g).edges.length → Bool) ≃ (Fin g.val.2.length → Bool) :=
    Equiv.arrowCongr (finCongr he) (Equiv.refl Bool)
  apply Fintype.sum_equiv e
  intro c
  let old : Fin g.val.2.length → Bool := fun i => c (Fin.cast he.symm i)
  have hc : Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend c=
      Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend old :=
    Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source.Literal.extend_cast he c
  rw [hc]
  change _=((OldCompiler.nodes g).map (fun p => Extensions.degreePartition p.1 (word g p.1 p.2 old))).prod
  simp only [Layout.virtual,List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  have ht (d : ℕ) (s : Bool) : ((2*d+Layout.tag s)%2==1)=s := by
    cases s <;> simp [Layout.tag]
  dsimp only [Function.comp_def]
  rw [ht,occurrence_word]

/-- Whole physical SAME emitted graph identity, without a caller value law.
All original occurrences, both self-loop ends and ordered boundary slots are
those of Layout.raw; no Eq graph or analytic leg is substituted. -/
theorem query_value (g : UnitInput) :
    targetValue (Layout.query g)=(2 : ℚ)^(Incidence.paddingCount g)*unitValue g := by
  rw [query_to_virtual,virtual_staged,staged_exact]
theorem query_corrected (g : UnitInput) :
    targetValue (Layout.query g)*((2 : ℚ)⁻¹)^(Incidence.paddingCount g)=unitValue g := by
  rw [query_to_virtual,virtual_staged]
  exact correction_exact g

end Semantics
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
