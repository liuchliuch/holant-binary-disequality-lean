import Holant.Complexity.FixedGadgetSubstitution.Incidence
import Holant.Complexity.FixedGadgetSubstitution.FiniteSemantics
import Holant.Complexity.ClosedNetworkCompleteness

/-! The actual serialized output of `replace` has exactly the denotation of
physical finite-gadget substitution. -/
noncomputable section
namespace Holant.Complexity.FixedGadgetSubstitution.RawSemantics
open RawClosedNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [CommSemiring K]
variable {sourceCount s b : ℕ} {arity : ℕ → ℕ}
variable (templates : ℕ → Template) (r : RawClosedNetwork)
variable (hr : r.WellFormed sourceCount b (sourceArity templates))
variable (hg : ∀ label < sourceCount, (templates label).WellFormed s b arity)
variable (source : (i : Fin sourceCount) → Signature K (sourceArity templates i.val))
variable (signatures : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

abbrev original : Network K 0 := r.realize hr source kernels

def gadgets (v : Fin r.vertices.length) : Network K (sourceArity templates (r.vertices.get v).1) :=
  (templates (r.vertices.get v).1).network (localWellFormed templates r hr hg v) signatures kernels

abbrev physical : Holant.FiniteNetwork K (Blocks (vertexSize templates) r.vertices)
    (Fin r.edges.length ⊕ Blocks (edgeSize templates) r.vertices) 0 :=
  Finite.network (original templates r hr source kernels) (gadgets templates r hr hg signatures kernels)


abbrev assignmentEquiv := Equiv.arrowCongr
  (Equiv.prodCongr (edgeOrder templates r) (Equiv.refl Bool)) (Equiv.refl Bool)

 theorem query_assignment (z : (Fin (replace templates r).edges.length × Bool) → Bool)
    (p : Blocks (vertexSize templates) r.vertices)
    (i : Fin (arity (localVertex templates r p).1)) :
    (replace templates r).route (query_wellFormed templates r hr hg) (queryPort templates r p i) =
      ((edgeOrder templates r).symm (attachment templates r hr hg p i).1,
        (attachment templates r hr hg p i).2) := by
  have h := query_route templates r hr hg p i
  have hh := congrArg (fun q => ((edgeOrder templates r).symm q.1,q.2)) h
  simpa using hh

/-- Every assignment read at an original query vertex port is unchanged. -/
 theorem assigned_port (z : (Fin (replace templates r).edges.length × Bool) → Bool)
    (p : Blocks (vertexSize templates) r.vertices)
    (i : Fin (arity (localVertex templates r p).1)) :
    z ((replace templates r).route (query_wellFormed templates r hr hg) (queryPort templates r p i)) =
      Sum.elim Fin.elim0 (assignmentEquiv templates r z)
        ((physical templates r hr hg source signatures kernels).ports ⟨p,i⟩) := by
  have h := congrFun (Finite.vertex_assignment
    (original templates r hr source kernels) (gadgets templates r hr hg signatures kernels)
    (assignmentEquiv templates r z) p.1 p.2) i
  refine Eq.trans ?_ h.symm
  rw [query_assignment templates r hr hg z p i]
  change _ = Sum.elim
    ((original templates r hr source kernels).shape.assignment Fin.elim0
      ((Finite.assignmentEquiv (original templates r hr source kernels)
        (gadgets templates r hr hg signatures kernels)) (assignmentEquiv templates r z)).1 p.1)
    (((Finite.assignmentEquiv (original templates r hr source kernels)
      (gadgets templates r hr hg signatures kernels)) (assignmentEquiv templates r z)).2 p.1)
    ((templates (r.vertices.get p.1).1).route (localWellFormed templates r hr hg p.1) ⟨p.2,i⟩)
  unfold attachment
  cases (templates (r.vertices.get p.1).1).route
    (localWellFormed templates r hr hg p.1) ⟨p.2,i⟩ <;> rfl

 theorem signatureLabel_at (p : Blocks (vertexSize templates) r.vertices) :
    (replace templates r).signatureLabel (query_wellFormed templates r hr hg)
      ((vertexOrder templates r).symm p) =
      ⟨(localVertex templates r p).1,
        (localWellFormed templates r hr hg p.1).1 _ (List.get_mem _ p.2) |>.1⟩ := by
  apply Fin.ext
  exact vertex_label templates r p

/-- The partition function of the exact emitted raw record is the physical
substitution value, under the original faithful decoder. -/
 theorem denote_query :
    ((replace templates r).realize (query_wellFormed templates r hr hg)
      signatures kernels).denote Fin.elim0 =
      (physical templates r hr hg source signatures kernels).denote Fin.elim0 := by
  classical
  letI : DecidableEq (Fin r.edges.length ⊕ Blocks (edgeSize templates) r.vertices) := Classical.decEq _
  unfold Network.denote Holant.FiniteNetwork.denote
  dsimp only [RawClosedNetwork.realize,RawClosedNetwork.shape]
  apply Fintype.sum_equiv (assignmentEquiv templates r)
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv (vertexOrder templates r)
    intro v
    obtain ⟨p,rfl⟩ := (vertexOrder templates r).symm.surjective v
    have hp := (vertexOrder templates r).apply_symm_apply p
    erw [hp]
    dsimp only [physical,Finite.network,gadgets,Template.network]
    apply ClosedLabelling.table_apply_congr signatures (signatureLabel_at templates r hr hg p)
    intro i
    let j : Fin (arity (localVertex templates r p).1) :=
      Fin.cast (congrArg arity (vertex_label templates r p)) i
    have h := assigned_port templates r hr hg source signatures kernels z p j
    convert h using 1 <;> rfl
  · apply Fintype.prod_equiv (edgeOrder templates r)
    intro e
    obtain ⟨j,rfl⟩ := (edgeOrder templates r).symm.surjective e
    cases j with
    | inl old =>
      have he : (replace templates r).edgeLabel (query_wellFormed templates r hr hg)
          ((edgeOrder templates r).symm (.inl old)) = r.edgeLabel hr old := by
        apply Fin.ext
        exact edge_at_order_old templates r old
      simp [RawClosedNetwork.realize,he,physical,Finite.network,original,assignmentEquiv]
    | inr inner =>
      have he : (replace templates r).edgeLabel (query_wellFormed templates r hr hg)
          ((edgeOrder templates r).symm (.inr inner)) =
          ⟨(templates (r.vertices.get inner.1).1).edges.get inner.2,
            (localWellFormed templates r hr hg inner.1).2.1 _ (List.get_mem _ inner.2)⟩ := by
        apply Fin.ext
        exact edge_at_order_new templates r inner
      simp [RawClosedNetwork.realize,he,physical,Finite.network,gadgets,Template.network,assignmentEquiv]

end Holant.Complexity.FixedGadgetSubstitution.RawSemantics
