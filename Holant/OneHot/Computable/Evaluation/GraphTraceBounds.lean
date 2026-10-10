import Holant.OneHot.Computable.Evaluation.Components
import Holant.OneHot.Computable.Evaluation.TraceBounds

/-!
# Intermediate values of the fully executable original-graph compiler

Bounds follow the actual emitted trees, residual programs and component products.
Equal final answers are never used as a substitute for controlling their traces.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.Computable.Evaluation OneHot.ArithmeticSize

variable {K A : Type*} [CommSemiring K] {coeff : A → K}
variable (N : Network K 0) (aone : A) (hone : coeff aone = 1)
include hone

/-- Actual computed tree syntax has a four-per-original-vertex budget, even
before assuming all original edges belong to the selected spanning tree. -/
theorem computedTreeProgram_bound (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * N.shape.vertices) (N.computedTreeProgram root hc).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * N.shape.vertices)) (N.computedTreeProgram root hc) := by
  let t := N.computedSpanning root hc
  let q := N.executableTree t N.shape.vertices
  have hb := tree_closed_program_bound aone hone q
    (N.executableTree_all t N.shape.vertices (Bound coeff 1) (Bound.zero aone 1) h)
  have hs := tree_spec t N.treeZero (N.executableParent t) (N.executableChild t)
    N.shape.vertices (N.computedSpanning_depth_le root hc)
  have hv : q.vertices = N.shape.vertices := hs.2.1
  have he : q.edges + 1 = N.shape.vertices := hs.2.2
  have hbudget : treeBudget q ≤ 4 * N.shape.vertices := by
    dsimp only [treeBudget]
    omega
  exact ⟨hb.1.mono aone hone hbudget, hb.2.mono (fun _ hx => hx.mono aone hone hbudget)⟩

end Holant.Network

namespace Holant.FiniteNetwork

open OneHot OneHot.Decomposition OneHot.ArithmeticSize

variable {K A V E : Type*} [CommSemiring K] [Fintype V] [Fintype E]
variable [LinearOrder V] [LinearOrder E] {coeff : A → K}
variable (N : FiniteNetwork K V E 0) (aone : A) (hone : coeff aone = 1)
include hone

theorem computedTreeProgram_bound (root : V)
    (hc : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * Fintype.card V) (N.computedTreeProgram root hc).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * Fintype.card V)) (N.computedTreeProgram root hc) :=
  N.orderedNetwork.computedTreeProgram_bound aone hone
    ((Fintype.orderIsoFinOfCardEq V rfl).symm root)
    (N.orderedNetwork_connected root hc)
    (fun v => h (Fintype.orderIsoFinOfCardEq V rfl v))

end Holant.FiniteNetwork

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.Computable.Evaluation OneHot.ArithmeticSize

variable {K A : Type*} [CommSemiring K] {coeff : A → K}
variable (N : Network K 0) (aone : A) (hone : coeff aone = 1)
include hone

/-- Conditioning fills original table arguments, preserving the fixed coefficient
family. The bound is on the actual executable conditioned-tree trace. -/
theorem executableConditionedProgram_bound {root : Fin N.shape.vertices}
    (t : RootedSpanning N.shape.endpoint root) (e : t.Surplus) (a b : Bool)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * N.shape.vertices) (N.executableConditionedProgram t e a b).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * N.shape.vertices)) (N.executableConditionedProgram t e a b) := by
  have hb := (N.asFinite.executableConditionEdge e.1 a b).computedTreeProgram_bound aone hone root
    (N.executableCondition_connected t e a b) (fun v x => h v _)
  unfold executableConditionedProgram
  convert! hb using 1 <;> simp only [Fintype.card_fin]

theorem executableSpanningUnicycleProgram_bound {root : Fin N.shape.vertices}
    (t : RootedSpanning N.shape.endpoint root) (e : t.Surplus)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * N.shape.vertices + 1) (N.executableSpanningUnicycleProgram t e).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * N.shape.vertices + 1)) (N.executableSpanningUnicycleProgram t e) := by
  rcases N.executableConditionedProgram_bound aone hone t e false true h with ⟨hx, hpx⟩
  rcases N.executableConditionedProgram_bound aone hone t e true false h with ⟨hy, hpy⟩
  have hz := hx.add aone hone hy
  refine ⟨?_, ?_⟩
  · simpa only [executableSpanningUnicycleProgram, bind, Arithmetic.run_bind, Arithmetic.run_addOp] using hz
  · apply Arithmetic.safe_bind (hpx.mono (fun _ hx => hx.mono aone hone (by omega)))
    apply Arithmetic.safe_bind (hpy.mono (fun _ hy => hy.mono aone hone (by omega)))
    exact Arithmetic.safe_addOp (hx.mono aone hone (by omega))
      (hy.mono aone hone (by omega)) hz

theorem computedConnectedProgram_bound (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * N.shape.vertices + 1) (N.computedConnectedProgram root hc).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * N.shape.vertices + 1)) (N.computedConnectedProgram root hc) := by
  unfold computedConnectedProgram
  split
  · exact ⟨Bound.zero aone _, Arithmetic.safe_pure _ _⟩
  · split
    · have hb := N.computedTreeProgram_bound aone hone root hc h
      exact ⟨hb.1.mono aone hone (by omega), hb.2.mono (fun _ hx => hx.mono aone hone (by omega))⟩
    · exact N.executableSpanningUnicycleProgram_bound aone hone _ _ h

/-- Bound the literal component program, using its original vertex fiber. -/
theorem computedComponentProgram_bound (root : Fin N.shape.vertices)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * Fintype.card (N.incidenceGraph.Fiber root) + 1)
      (N.computedComponentProgram root).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * Fintype.card (N.incidenceGraph.Fiber root) + 1))
      (N.computedComponentProgram root) :=
  (N.computedComponentNetwork root).computedConnectedProgram_bound aone hone _
    ((N.computedComponent root).orderedNetwork_connected _ (N.computedComponent_connected root))
    (fun _v _x => h _ _)

/-- Every executed operand/result and final output of the complete executable
component compiler has a budget linear in the original vertex count. -/
theorem computedOneHotProgram_bound (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (5 * N.shape.vertices) N.computedOneHotProgram.run.1 ∧
    Arithmetic.Safe (Bound coeff (5 * N.shape.vertices)) N.computedOneHotProgram := by
  classical
  let en := N.computedRootOrder.trans N.computedRootEquiv
  let b (i : Fin (Fintype.card N.ComputedRoot)) :=
    4 * Fintype.card (N.incidenceGraph.Fiber (N.computedRootOrder i).1) + 1
  have hb := finiteProduct_bound aone hone
    (fun i => N.computedComponentProgram (N.computedRootOrder i).1) b
    (fun i => N.computedComponentProgram_bound aone hone (N.computedRootOrder i).1 h)
  have hcard (i : Fin (Fintype.card N.ComputedRoot)) :
      Fintype.card (N.incidenceGraph.Fiber (N.computedRootOrder i).1) =
        Fintype.card (N.shape.ComponentVertex (en i)) :=
    Fintype.card_congr (N.computedComponentVertices (N.computedRootOrder i).1)
  have hbudget : (∑ i, b i) ≤ 5 * N.shape.vertices := by
    have hc : Fintype.card N.ComputedRoot ≤ N.shape.vertices := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        (fun v : N.ComputedRoot => v.1) Subtype.val_injective
    have hs : (∑ i, b i) = 4 * N.shape.vertices + Fintype.card N.ComputedRoot := by
      simp only [b, hcard, Finset.sum_add_distrib, ← Finset.mul_sum,
        en.sum_comp (fun c => Fintype.card (N.shape.ComponentVertex c)),
        N.shape.sum_componentVertex_card, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  exact ⟨hb.1.mono aone hone hbudget, hb.2.mono (fun _ hx => hx.mono aone hone hbudget)⟩

end Holant.Network

namespace Holant.Network

open OneHot OneHot.ArithmeticSize

variable {K A : Type*} [Field K] [Algebra ℚ K] {n : ℕ} [Fintype A]
variable (F : Algebraic.FixedField K n) (coeff : A → Fin n → ℚ) (N : Network K 0)

/-- Faithful binary bounds on every ACTUAL value of the newly executable whole
graph program. This still makes no uniform-machine runtime claim. -/
theorem computedOneHotProgram_encoded_length_le
    (h : ∀ v x, ∃ a, N.vertex v x = F.decode (coeff a)) :
    (F.encoding.encode N.computedOneHotProgram.run.1).length ≤
      bitBound F (withUnit F coeff) (5 * N.shape.vertices) ∧
    ∀ x ∈ N.computedOneHotProgram.values, (F.encoding.encode x).length ≤
      bitBound F (withUnit F coeff) (5 * N.shape.vertices) := by
  have hb := N.computedOneHotProgram_bound none (decode_withUnit_none F coeff)
    (fun v x => family_bound F coeff (h v x))
  exact ⟨hb.1.encoded_length_le F (withUnit F coeff),
    fun x hx => (hb.2 x hx).encoded_length_le F (withUnit F coeff)⟩

end Holant.Network

namespace Holant.Complexity.RawClosedNetwork

open OneHot OneHot.ArithmeticSize

variable {K A : Type*} [Field K] [Algebra ℚ K] {n s b : ℕ} [Fintype A]
variable {arity : ℕ → ℕ} (F : Algebraic.FixedField K n) (coeff : A → Fin n → ℚ)
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

/-- Intermediate and output encoding lengths in the actual framed input length,
for the executable program the decoder/compiler returns on this record. -/
theorem compiled_encoded_length_le
    (hf : ∀ i x, ∃ a, signatures i x = F.decode (coeff a)) :
    let p := (r.executableRealize h signatures kernels).computedOneHotProgram
    (F.encoding.encode p.run.1).length ≤
      bitBound F (withUnit F coeff) (5 * (encoding.encode r).length) ∧
    ∀ x ∈ p.values, (F.encoding.encode x).length ≤
      bitBound F (withUnit F coeff) (5 * (encoding.encode r).length) := by
  have hb := (r.executableRealize h signatures kernels).computedOneHotProgram_encoded_length_le
    F coeff (fun v x => hf (r.signatureLabel h v) x)
  have hv : r.vertices.length ≤ (encoding.encode r).length := by
    have hh := r.counts_le_encoded_length
    omega
  have hm := bitBound_mono F (withUnit F coeff) (Nat.mul_le_mul_left 5 hv)
  exact ⟨hb.1.trans hm, fun x hx => (hb.2 x hx).trans hm⟩

end Holant.Complexity.RawClosedNetwork
