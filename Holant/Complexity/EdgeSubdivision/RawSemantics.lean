import Holant.Complexity.EdgeSubdivision.Incidence
import Holant.Complexity.EdgeSubdivision.Labels
import Holant.Complexity.ClosedNetworkCompleteness

/-! Exact semantic identity for the raw bytes produced by edge subdivision. -/
noncomputable section
namespace Holant.Complexity.EdgeSubdivision
open RawClosedNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommSemiring K] {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (hr : r.WellFormed s b arity)
variable (source : (i : Fin s) → Signature K (arity i.val))
variable (kernels binary : Fin b → Bool → Bool → K) (wire : Bool → Bool → K)

abbrev original := r.realize hr source kernels
abbrev physical := Finite.network (original r hr source kernels)
  (fun e => binary (r.edgeLabel hr e)) wire

def localLabel : (Fin r.vertices.length ⊕ Fin r.edges.length) → Fin (s+b) :=
  Sum.elim (fun v => Fin.castAdd b (r.signatureLabel hr v))
    (fun e => Fin.natAdd s (r.edgeLabel hr e))

theorem localLabel_val (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    (localLabel r hr p).val = (localVertex s r p).1 := by cases p <;> rfl

theorem localLabel_arity (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    targetArity s arity (localLabel r hr p).val = localArity (arity:=arity) r p := by
  rw [localLabel_val]
  exact localArity_eq s r hr p

theorem extended_vertex (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (x : Fin (targetArity s arity (localLabel r hr p).val) → Bool) :
    extendedSignatures source binary (localLabel r hr p) x =
      (physical r hr source kernels binary wire).vertex p
        (fun i => x (Fin.cast (localLabel_arity r hr p).symm i)) := by
  cases p with
  | inl v =>
    change extendedSignatures source binary (Fin.castAdd b (r.signatureLabel hr v)) x = _
    rw [extendedSignatures_old]
    rfl
  | inr e =>
    change extendedSignatures source binary (Fin.natAdd s (r.edgeLabel hr e)) x = _
    rw [extendedSignatures_new]
    rfl

theorem physical_ports (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (i : Fin (localArity (arity:=arity) r p)) :
    (physical r hr source kernels binary wire).ports ⟨p,i⟩ = .inr (attachment s r hr p i) := by
  cases p with
  | inl v =>
    simp [physical,Finite.network,Finite.ports,Finite.arity,original,RawClosedNetwork.realize,
      RawClosedNetwork.shape,RawClosedNetwork.closedEndsEquiv,Equiv.sumSigmaDistrib,
      Finite.halfEnds,Equiv.emptySum,attachment,RawClosedNetwork.portEquiv]
  | inr e =>
    change Fin 2 at i
    fin_cases i <;>
      simp [physical,Finite.network,Finite.ports,Finite.arity,Equiv.sumSigmaDistrib,
        Equiv.sigmaEquivProd,Finite.halfEnds,Equiv.emptySum,attachment,finTwoEquiv]

abbrev assignmentEquiv := Equiv.arrowCongr
  (Equiv.prodCongr (edgeOrder s r) (Equiv.refl Bool)) (Equiv.refl Bool)

theorem assigned_port (z : (Fin (subdivide s r).edges.length×Bool) → Bool)
    (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (i : Fin (localArity (arity:=arity) r p)) :
    z ((subdivide s r).route (queryValid s r hr) (orderedPort s r hr p i)) =
      Sum.elim Fin.elim0 (assignmentEquiv r z)
        ((physical r hr source kernels binary wire).ports ⟨p,i⟩) := by
  rw [query_route,physical_ports]
  rfl

theorem query_label (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    (subdivide s r).signatureLabel (queryValid s r hr) ((vertexOrder s r).symm p) =
      localLabel r hr p := by
  apply Fin.ext
  exact (vertex_label s r p).trans (localLabel_val r hr p).symm

def localBits (z : (Fin (subdivide s r).edges.length×Bool) → Bool)
    (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    Fin (targetArity s arity (localLabel r hr p).val) → Bool :=
  fun i => z ((subdivide s r).route (queryValid s r hr)
    (orderedPort s r hr p (Fin.cast (localLabel_arity r hr p) i)))

theorem local_vertex_weight (z : (Fin (subdivide s r).edges.length×Bool) → Bool)
    (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    extendedSignatures source binary (localLabel r hr p) (localBits r hr z p) =
      (physical r hr source kernels binary wire).vertex p
        (fun i => Sum.elim Fin.elim0 (assignmentEquiv r z)
          ((physical r hr source kernels binary wire).ports ⟨p,i⟩)) := by
  rw [extended_vertex r hr source kernels binary wire]
  congr 1
  funext i
  simpa only [localBits,Fin.cast_cast,Fin.cast_refl,id_eq] using
    assigned_port r hr source kernels binary wire z p i

theorem query_vertex_weight (z : (Fin (subdivide s r).edges.length×Bool) → Bool)
    (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    extendedSignatures source binary
      ((subdivide s r).signatureLabel (queryValid s r hr) ((vertexOrder s r).symm p))
      (fun i => z ((subdivide s r).route (queryValid s r hr)
        ⟨(vertexOrder s r).symm p,i⟩)) =
      (physical r hr source kernels binary wire).vertex p
        (fun i => Sum.elim Fin.elim0 (assignmentEquiv r z)
          ((physical r hr source kernels binary wire).ports ⟨p,i⟩)) := by
  rw [←local_vertex_weight r hr source kernels binary wire z p]
  apply ClosedLabelling.table_apply_congr (extendedSignatures source binary) (query_label r hr p)
  intro i
  rfl

/-- The compiler's actual emitted graph has the subdivision network's exact
partition value, before applying a local matrix identity. -/
theorem denote_query :
    ((subdivide s r).realize (queryValid s r hr) (extendedSignatures source binary)
      (fun _ => wire)).denote Fin.elim0 =
      (physical r hr source kernels binary wire).denote Fin.elim0 := by
  classical
  letI : DecidableEq (Fin r.edges.length×Bool) := Classical.decEq _
  unfold Network.denote Holant.FiniteNetwork.denote
  dsimp only [RawClosedNetwork.realize,RawClosedNetwork.shape]
  apply Fintype.sum_equiv (assignmentEquiv r)
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv (vertexOrder s r)
    intro v
    obtain ⟨p,rfl⟩ := (vertexOrder s r).symm.surjective v
    erw [(vertexOrder s r).apply_symm_apply p]
    exact query_vertex_weight r hr source kernels binary wire z p
  · apply Fintype.prod_equiv (edgeOrder s r)
    intro e
    obtain ⟨p,rfl⟩ := (edgeOrder s r).symm.surjective e
    simp [physical,Finite.network,assignmentEquiv]

/-- Exact source value for every validated raw input, including scalar-only
components, loops and parallel edges. -/
theorem subdivision_partition_value
    (hfuse : ∀ j a c, (∑ uv : Bool×Bool,
      wire a uv.1 * binary j uv.1 uv.2 * wire uv.2 c) = kernels j a c) :
    ((subdivide s r).realize (queryValid s r hr) (extendedSignatures source binary)
      (fun _ => wire)).denote Fin.elim0 =
      (r.realize hr source kernels).denote Fin.elim0 := by
  rw [denote_query r hr source kernels binary wire]
  apply Finite.denote
  intro e a c
  exact hfuse (r.edgeLabel hr e) a c

end Holant.Complexity.EdgeSubdivision
