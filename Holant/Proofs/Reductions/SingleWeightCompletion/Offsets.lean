import Holant.Proofs.Reductions.SingleWeightCompletion.UniqueExtension


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.Offsets
open Holant.Complexity FixedGadgetSubstitution.Compiler
open scoped BigOperators
variable {s : ℕ} {a : ℕ → ℕ} (d : Fin s → ℕ)

def weight (b : Bool) : ℕ → ℕ :=
  if b then ChargeProgram.oneWeight (a:=a) d else ChargeProgram.zeroWeight (a:=a) d
def base (x : Query s 1 a) : ℕ :=
  ((List.finRange x.1.val.vertices.length).map fun v =>
    if component x.1 v < component x.1 x.2 then weight (a:=a) d false (x.1.val.vertices.get v).1 else 0).sum
def «prefix» (b : Bool) (x : Query s 1 a) : ℕ :=
  ((List.finRange x.1.val.vertices.length).map fun v =>
    if component x.1 v=component x.1 x.2 ∧ v.val<x.2.val then weight (a:=a) d b (x.1.val.vertices.get v).1 else 0).sum
def edgeBase (b : Bool) (x : Query s 1 a) : ℕ := x.1.val.edges.length+base d x+«prefix» d b x

theorem prefix_sum {n : ℕ} (f : Fin n → ℕ) (v : Fin n) :
    (∑ i : Fin v.val, f (Fin.castLE v.isLt.le i)) = ∑ i : Fin n, if i.val<v.val then f i else 0 := by
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => Fin.castLE v.isLt.le i)
  · intro i _; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]; exact i.isLt
  · intro i _ j _ h; exact Fin.ext (congrArg (fun z : Fin n => z.val) h)
  · intro j hj
    refine ⟨⟨j.val,(Finset.mem_filter.mp hj).2⟩,Finset.mem_univ _,?_⟩
    exact Fin.ext rfl
  · intro i _; rfl

theorem weight_vertex (r : Input (s:=s) (a:=a)) (v : Fin r.val.vertices.length) (b : Bool) :
    weight (a:=a) d b (r.val.vertices.get v).1 =
      if CompletedGraph.side d r v=b then CompletedGraph.added d r v else 0 := by
  have hlabel := (r.property.1 v).1
  simp only [List.get_eq_getElem] at hlabel
  cases b <;> cases hb : CompletedGraph.side d r v <;>
    simp [weight,ChargeProgram.zeroWeight,ChargeProgram.oneWeight,(r.property.1 v).1,
      CompletedGraph.side,CompletedGraph.added,CompletedGraph.label,RawClosedNetwork.signatureLabel] at hb ⊢ <;> simp_all

theorem base_formula (r : Input (s:=s) (a:=a)) (v : Fin r.val.vertices.length) : base d ⟨r,v⟩ =
    ∑ c : Fin (CompletedGraph.color r v).val,
      SlotRouting.size (CompletedGraph.added d r) (CompletedGraph.side d r) (CompletedGraph.color r)
        (Fin.castLE (CompletedGraph.color r v).isLt.le c) false := by
  rw [prefix_sum (fun c : Fin r.val.vertices.length =>
    SlotRouting.size (CompletedGraph.added d r) (CompletedGraph.side d r) (CompletedGraph.color r) c false)
    (CompletedGraph.color r v)]
  have hd (c : Fin r.val.vertices.length) :
      (if c.val<(CompletedGraph.color r v).val then
        SlotRouting.size (CompletedGraph.added d r) (CompletedGraph.side d r) (CompletedGraph.color r) c false else 0) =
      ∑ u : Fin r.val.vertices.length, if c.val<(CompletedGraph.color r v).val then
        SlotRouting.mass (CompletedGraph.added d r) (CompletedGraph.side d r) (CompletedGraph.color r) c false u else 0 := by
    by_cases hc : c.val<(CompletedGraph.color r v).val <;> simp [hc,SlotRouting.size]
  simp only [hd]
  rw [Finset.sum_comm]
  simp only [base,←List.ofFn_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro u _
  rw [weight_vertex]
  have he : (∑ c : Fin r.val.vertices.length,
      if c.val<(CompletedGraph.color r v).val then
        SlotRouting.mass (CompletedGraph.added d r) (CompletedGraph.side d r) (CompletedGraph.color r) c false u else 0) =
      if (CompletedGraph.color r u).val<(CompletedGraph.color r v).val then
        (if CompletedGraph.side d r u=false then CompletedGraph.added d r u else 0) else 0 := by
    rw [Finset.sum_eq_single (CompletedGraph.color r u)]
    · simp [SlotRouting.mass]
    · intro c _ hc
      simp [SlotRouting.mass,Ne.symm hc]
    · simp
  exact he.symm

theorem prefix_formula (r : Input (s:=s) (a:=a)) (v : Fin r.val.vertices.length) (b : Bool) :
    «prefix» d b ⟨r,v⟩ = ∑ u : Fin v.val,
      SlotRouting.mass (CompletedGraph.added d r) (CompletedGraph.side d r) (CompletedGraph.color r)
        (CompletedGraph.color r v) b (Fin.castLE v.isLt.le u) := by
  rw [prefix_sum]
  simp only [«prefix»,←List.ofFn_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro u _
  rw [weight_vertex]
  have he : component r u=component r v ↔ CompletedGraph.color r u=CompletedGraph.color r v := Fin.ext_iff.symm
  by_cases hc : component r u=component r v
  · have hc' := he.mp hc
    by_cases hi : u.val<v.val <;> simp [SlotRouting.mass,hc,hc',hi]
  · have hc' : CompletedGraph.color r u≠CompletedGraph.color r v := fun h => hc (he.mpr h)
    by_cases hi : u.val<v.val <;> simp [SlotRouting.mass,hc,hc',hi]

theorem route_formula (r : Input (s:=s) (a:=a)) (h : Balanced d r)
    (p : CompletedGraph.slots d r) :
    r.val.edges.length+(CompletedGraph.addedRoute d r h p).1.val =
      edgeBase d (CompletedGraph.side d r p.1) ⟨r,p.1⟩+p.2.val := by
  rw [SlotRouting.route_index,←base_formula,←prefix_formula]
  simp only [edgeBase,Nat.add_assoc]

theorem total_formula (r : Input (s:=s) (a:=a)) : CompletedGraph.newCount d r =
    (r.val.vertices.map fun row => weight (a:=a) d false row.1).sum := by
  have hrows : (r.val.vertices.map fun row => weight (a:=a) d false row.1).sum =
      ∑ v : Fin r.val.vertices.length, weight (a:=a) d false (r.val.vertices.get v).1 := by
    calc
      _ = (List.ofFn (fun v : Fin r.val.vertices.length =>
          weight (a:=a) d false (r.val.vertices.get v).1)).sum :=
        congrArg List.sum (List.ofFn_getElem_eq_map r.val.vertices
          (fun row => weight (a:=a) d false row.1)).symm
      _ = _ := List.sum_ofFn
  rw [hrows]
  unfold CompletedGraph.newCount SlotRouting.total SlotRouting.size
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [weight_vertex,Finset.sum_eq_single (CompletedGraph.color r v)]
  · simp [SlotRouting.mass]
  · intro c _ hc; simp [SlotRouting.mass,Ne.symm hc]
  · simp

end Holant.LocalDrafts.Hardness.SingleWeightCompletion.Offsets
