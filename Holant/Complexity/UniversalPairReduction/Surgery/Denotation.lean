import Holant.Complexity.UniversalPairReduction.Surgery.NativeSmoothing
import Holant.Complexity.UniversalPairReduction.BinaryFamily

/-! Exact denotation of the literal raw smoothing output, joined to the original
faithful decoder. The loop scalar comes from its two actual edge choices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.Surgery
open FixedGadgetSubstitution RawClosedNetwork Smoothing Choice
variable {K : Type*} [CommSemiring K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (r : Input s arity) (v : Fin r.val.vertices.length)
variable (hv : (r.val.vertices.get v).1=s)
variable (p q : RawEndpoint) (hrow : (r.val.vertices.get v).2=[p,q])

def queryAt : {r : RawClosedNetwork // r.WellFormed s 1 arity} :=
  ⟨(smoothAt r.val v.val p q).query,
    smoothAt_wellFormed r.val r.property.1 v p q hrow (erased_valid r v hv)⟩

def targetValue (a : {r : RawClosedNetwork // r.WellFormed s 1 arity}) : K :=
  (a.val.realize a.property G (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0

include hv hrow in
 theorem record_partition :
    ((s,[p,q])::r.val.vertices.eraseIdx v.val).Perm r.val.vertices := by
  have hh : r.val.vertices[v.val]=(s,[p,q]) := Prod.ext hv hrow
  simpa only [hh] using List.getElem_cons_eraseIdx_perm v.isLt

 theorem remainder_member (row : RawVertex) (hr : row∈r.val.vertices.eraseIdx v.val)
    (t : RawEndpoint) (ht : t∈row.2) : t∈remainderEnds r.val v.val :=
  List.mem_flatten.mpr ⟨row.2,List.mem_map.mpr ⟨row,hr,rfl⟩,ht⟩

include hv in
 theorem remap_labels (f : RawEndpoint → RawEndpoint) :
    ∀row∈Choice.mapRows f (r.val.vertices.eraseIdx v.val),row.1<s := by
  intro row hrow
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hrow
  exact (erased_valid r v hv old ho).1

include hrow in
 theorem loop_mate (he : p.1=q.1) : q=(p.1,!p.2) := by
  have hp := marked_endpoint_partition r.val r.property.1 v p q hrow
  have hneq : p≠q := by
    have hn := hp.symm.nodup (ends_nodup _)
    exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  apply Prod.ext
  · exact he.symm
  · rcases p with ⟨e,a⟩
    rcases q with ⟨f,b⟩
    dsimp at he ⊢
    subst f
    cases a <;> cases b <;> simp_all

/-- If the two marked occurrences share an edge, every original binary B
contributes its exact off-diagonal trace times the retained target components. -/
theorem loop_value (B : BinaryTable K) (he : p.1=q.1) :
    BinaryFamily.value G B r = (B false true+B true false)*targetValue G (queryAt r v hv p q hrow) := by
  have hp := marked_endpoint_partition r.val r.property.1 v p q hrow
  have hpbound : p.1<r.val.edges.length := (ends_mem _ _).mp (hp.mem_iff.mp (by simp))
  have hmate := loop_mate r v p q hrow he
  have hrem := (loop_remainder r.val.edges.length p.1 p.2 (remainderEnds r.val v.val)
    (by simpa only [hmate] using hp)).2
  rw [BinaryFamily.value_evaluate]
  rw [←Choice.evaluate_perm _ _ (record_partition r v hv p q hrow)]
  conv_lhs => rw [hmate]
  have hx := Choice.evaluate_loop (Choice.table (BinaryFamily.signatures G B)) r.val.edges.length s p.1 hpbound p.2 B
    (r.val.vertices.eraseIdx v.val) (fun row hr t ht =>
      (hrem t).mp (remainder_member r v row hr t ht)) (BinaryFamily.table_pair G B)
  rw [hx]
  congr 1
  rw [BinaryFamily.evaluate_old G B _ _ (remap_labels r v hv _)]
  unfold targetValue
  rw [Choice.denote_eq_evaluate]
  change _ = Choice.evaluate _ (smoothAt r.val v.val p q).query.edges.length
    (smoothAt r.val v.val p q).query.vertices
  simp only [smoothAt,ite_eq_left he,emit]
  rw [List.length_eraseIdx_of_lt hpbound]
  rfl

/-- Distinct native-X attachments smooth to precisely one native-X edge,
including the case where its far ends become a self-loop. -/
theorem splice_value (he : p.1≠q.1) :
    BinaryFamily.value G Signature.disequality r=targetValue G (queryAt r v hv p q hrow) := by
  have hp := marked_endpoint_partition r.val r.property.1 v p q hrow
  have hpbound : p.1<r.val.edges.length := (ends_mem _ _).mp (hp.mem_iff.mp (by simp))
  have hqbound : q.1<r.val.edges.length := (ends_mem _ _).mp (hp.mem_iff.mp (by simp))
  rw [BinaryFamily.value_evaluate]
  rw [←Choice.evaluate_perm _ _ (record_partition r v hv p q hrow)]
  have hx := Choice.evaluate_splice (Choice.table (BinaryFamily.signatures G Signature.disequality))
    r.val.edges.length s p q (r.val.vertices.eraseIdx v.val) hpbound hqbound he (by
      intro row hr t ht
      have hmem := remainder_member r v row hr t ht
      exact ⟨(ends_mem _ t).mp (hp.mem_iff.mp (by simp [hmem])),
        remainder_ne _ p q _ hp t hmem⟩) (BinaryFamily.table_pair G Signature.disequality)
  rw [hx,BinaryFamily.evaluate_old G Signature.disequality _ _ (remap_labels r v hv _)]
  unfold targetValue
  rw [Choice.denote_eq_evaluate]
  change _ = Choice.evaluate _ (smoothAt r.val v.val p q).query.edges.length
    (smoothAt r.val v.val p q).query.vertices
  simp only [smoothAt,ite_eq_right he,emit]
  rw [List.length_eraseIdx_of_lt hqbound]
  rfl

/-- The raw compiler's circle bit accounts for its entire normalization. -/
theorem native_value :
    BinaryFamily.value G Signature.disequality r =
      (if (smoothAt r.val v.val p q).circle then 2 else 1)*targetValue G (queryAt r v hv p q hrow) := by
  by_cases he : p.1=q.1
  · rw [loop_value G r v hv p q hrow Signature.disequality he]
    simp [smoothAt,he,Signature.disequality,two_mul,add_mul]
  · rw [splice_value G r v hv p q hrow he]
    simp [smoothAt,he]

end Holant.Complexity.UniversalPairReduction.Surgery
