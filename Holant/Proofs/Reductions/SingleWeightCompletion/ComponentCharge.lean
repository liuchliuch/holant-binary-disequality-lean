import Holant.Proofs.Reductions.SingleWeightCompletion.Family
import Holant.ChargeConservation
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel
import Holant.OneHot.Computable.RawBridge


noncomputable section
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion
open Holant.Complexity
open scoped BigOperators

def spin (b : Bool) : ℤ := if b then 1 else -1
theorem charge_sum {n : ℕ} (x : Fin n → Bool) : charge x = ∑ i, spin (x i) := by
  have hb (b : Bool) : spin b = 2*(if b then (1:ℤ) else 0)-1 := by cases b <;> rfl
  simp only [hb,Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  simp [charge,weight]

theorem colored_conservation (S : NetworkShape 0) (color : Fin S.vertices → ℕ)
    (hc : ∀ e b, color (S.endpoint e b) = color (S.endpoint e false))
    (z : (Fin S.edges × Bool) → Bool) (hz : ∀ e, z (e,false) ≠ z (e,true)) (c : ℕ) :
    (∑ v, if color v=c then charge (S.assignment Fin.elim0 z v) else 0) = 0 := by
  have hp : (∑ v, if color v=c then charge (S.assignment Fin.elim0 z v) else 0) =
      ∑ p : (Σ v : Fin S.vertices, Fin (S.arity v)),
        if color p.1=c then spin (z (S.closedPorts p)) else 0 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : color v=c <;> simp [h,charge_sum,NetworkShape.assignment_closed]
  rw [hp,←S.closedPorts.symm.sum_comp (fun p => if color p.1=c then spin (z (S.closedPorts p)) else 0)]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro e _
  change (∑ b : Bool, if color (S.endpoint e b)=c then spin (z (e,b)) else 0) = 0
  simp only [hc,Fintype.sum_bool]
  by_cases h : color (S.endpoint e false)=c
  · have hh := hz e
    cases h0 : z (e,false) <;> cases h1 : z (e,true) <;> simp_all [spin]
  · simp [h]

variable {K : Type} [Field K]
theorem colored_imbalance (G : Network K 0) (hX : ∀ e, G.edge e=Signature.disequality)
    (color : Fin G.shape.vertices → ℕ)
    (hc : ∀ e b, color (G.shape.endpoint e b)=color (G.shape.endpoint e false))
    (d : Fin G.shape.vertices → ℕ) (hd : ∀ v, Signature.SingleLayer (G.vertex v) (d v))
    (c : ℕ) (hbad : (∑ v, if color v=c then 2*(d v:ℤ)-G.shape.arity v else 0) ≠ 0) :
    G.denote Fin.elim0 = 0 := by
  change (∑ z, G.assignmentTerm Fin.elim0 z) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_contra hn
  have hop (e) : z (e,false) ≠ z (e,true) := by
    intro he
    have hh := G.edge_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 z hn e
    rw [hX] at hh
    exact hh (by simp [Signature.disequality,he])
  have hw (v) : weight (G.shape.assignment Fin.elim0 z v)=d v :=
    (hd v).weight_of_nezero (G.vertex_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 z hn v)
  exact hbad (by simpa only [charge,hw] using colored_conservation G.shape color hc z hop c)

variable {s : ℕ} {a : ℕ → ℕ}
abbrev Input := ExactSignatureTables.Input s 1 a
def component (r : Input (s:=s) (a:=a)) (v : Fin r.val.vertices.length) : ℕ :=
  ((r.val.graph r.property).label v).val
def chargeAt (d : Fin s → ℕ) (r : Input (s:=s) (a:=a)) (v : Fin r.val.vertices.length) : ℤ :=
  2*(d (r.val.signatureLabel r.property v):ℤ) - a (r.val.vertices.get v).1
def componentCharge (d : Fin s → ℕ) (r : Input (s:=s) (a:=a)) (c : ℕ) : ℤ :=
  ∑ v, if component r v=c then chargeAt d r v else 0
def Balanced (d : Fin s → ℕ) (r : Input (s:=s) (a:=a)) : Prop :=
  ∀ v, componentCharge d r (component r v) = 0

theorem component_edge (r : Input (s:=s) (a:=a)) (e : Fin r.val.edges.length) (b : Bool) :
    component r ((r.val.shape r.property).endpoint e b) =
      component r ((r.val.shape r.property).endpoint e false) := by
  have hh := (r.val.graph r.property).endpoint_labels ((r.val.graphEdgeEquiv r.property).symm e) b
  simp only [RawClosedNetwork.graph_endpoint,Equiv.apply_symm_apply] at hh
  exact congrArg Fin.val hh

theorem reject_value (G : (i : Fin s) → Signature K (a i.val)) (d : Fin s → ℕ)
    (hd : ∀ i, Signature.SingleLayer (G i) (d i)) (r : Input (s:=s) (a:=a))
    (h : ¬ Balanced d r) : (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0 = 0 := by
  obtain ⟨v,hv⟩ := not_forall.mp h
  exact colored_imbalance (r.val.realize r.property G (fun _ => Signature.disequality))
    (fun _ => rfl) (component r) (component_edge r)
    (fun w => d (r.val.signatureLabel r.property w))
    (fun w => by
      change Signature.SingleLayer (G (r.val.signatureLabel r.property w))
        (d (r.val.signatureLabel r.property w))
      exact hd (r.val.signatureLabel r.property w)) (component r v) hv

theorem all_vertices (r : Input (s:=s) (a:=a)) (v : Fin r.val.vertices.length) :
    ∃! c : Fin r.val.vertices.length, (r.val.graph r.property).label c=c ∧ component r v=c.val := by
  refine ⟨(r.val.graph r.property).label v,⟨(r.val.graph r.property).label_idempotent v,rfl⟩,?_⟩
  intro c hc
  exact Fin.ext hc.2.symm

end Holant.LocalDrafts.Hardness.SingleWeightCompletion
