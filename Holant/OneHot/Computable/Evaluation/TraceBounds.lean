import Holant.OneHot.Computable.Evaluation.Provenance
import Holant.OneHot.ArithmeticSizeEncoding

/-! Actual executable-tree coefficient provenance and intermediate trace bounds. -/

namespace Holant.OneHot.Computable.Evaluation

variable {K α : Type*}

theorem ofList_all (P : K → Prop) (port : α → K) (trees : α → Tree K)
    (hp : ∀ u, P (port u)) (ht : ∀ u, (trees u).All P) (us : List α) :
    (Summary.ofList port trees us).All P := by
  induction us with
  | nil => trivial
  | cons u us ih => exact ⟨hp u, ht u, ih⟩

variable {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}
variable (t : Holant.OneHot.Decomposition.RootedSpanning endpoint root)

/-- Predicate on every literal coefficient of the computed syntax, not merely
on its denotation or returned value. -/
theorem build_all (P : K → Prop) (a b : Fin n → K)
    (port : {u : Fin n // u ≠ root} → K)
    (ha : ∀ v, P (a v)) (hb : ∀ v, P (b v)) (hp : ∀ u, P (port u))
    (fuel : ℕ) (v : Fin n) : (build t a b port fuel v).All P := by
  induction fuel generalizing v with
  | zero => exact ⟨ha v, hb v, trivial⟩
  | succ fuel ih =>
    exact ⟨ha v, hb v, ofList_all P _ _ (fun u : Child t v => hp ⟨u.1, u.2.1⟩)
      (fun u : Child t v => ih u.1) _⟩

end Holant.OneHot.Computable.Evaluation

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.Computable.Evaluation OneHot.ArithmeticSize

variable {K : Type*} [CommSemiring K] (N : Network K 0)
variable {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)

/-- The actual emitted tree carries only literal original input coefficients and
the root's unused zero coefficient. This controls its real arithmetic trace. -/
theorem executableTree_all (maxDepth : ℕ) (P : K → Prop)
    (hz : P 0) (hf : ∀ v x, P (N.vertex v x)) :
    (N.executableTree t maxDepth).All P := by
  apply build_all t P
  · exact fun v => hf v _
  · intro v
    unfold executableParent
    split
    · exact hz
    · exact hf _ _
  · intro u
    exact hf _ _

/-- Every executed operand/result of the executable closed-tree program has a
linear structural expansion budget. No semantic-program trace is substituted. -/
theorem executableTree_bound {A : Type*} {coeff : A → K}
    (aone : A) (hone : coeff aone = 1) (maxDepth : ℕ)
    (bound : ∀ v, t.depth v ≤ maxDepth)
    (htree : N.shape.edges + 1 = N.shape.vertices)
    (hf : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (2 * (N.shape.vertices + N.shape.edges))
      (N.executableTree t maxDepth).closedProgram.run.1 ∧
    Arithmetic.Safe (Bound coeff (2 * (N.shape.vertices + N.shape.edges)))
      (N.executableTree t maxDepth).closedProgram := by
  have ha := N.executableTree_all t maxDepth (Bound coeff 1) (Bound.zero aone 1) hf
  have hs := tree_spec t N.treeZero (N.executableParent t) (N.executableChild t) maxDepth bound
  have hv : (N.executableTree t maxDepth).vertices = N.shape.vertices := hs.2.1
  have he : (N.executableTree t maxDepth).edges = N.shape.edges := by
    have hh : (N.executableTree t maxDepth).edges + 1 = N.shape.vertices := hs.2.2
    omega
  have hbudget : treeBudget (N.executableTree t maxDepth) =
      2 * (N.shape.vertices + N.shape.edges) := by rw [treeBudget, hv, he]
  rw [← hbudget]
  generalize hq : N.executableTree t maxDepth = q at ha ⊢
  cases q with
  | node a b ts =>
    simpa only [treeBudget_node, Tree.closedProgram] using
      closed_program_bound aone hone ts a ha.2.2 ha.1

end Holant.Network

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.ArithmeticSize

variable {K A : Type*} [Field K] [Algebra ℚ K] {n : ℕ} [Fintype A]
variable (F : Algebraic.FixedField K n) (coeff : A → Fin n → ℚ) (N : Network K 0)
variable {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)

/-- Faithful binary lengths of the result AND every executed arithmetic value,
measured on the original graph, for the genuinely executable emitted program. -/
theorem executableTree_encoded_length_le (maxDepth : ℕ)
    (bound : ∀ v, t.depth v ≤ maxDepth)
    (htree : N.shape.edges + 1 = N.shape.vertices)
    (hf : ∀ v x, ∃ a, N.vertex v x = F.decode (coeff a)) :
    (F.encoding.encode (N.executableTree t maxDepth).closedProgram.run.1).length ≤
      bitBound F (withUnit F coeff) (2 * (N.shape.vertices + N.shape.edges)) ∧
    ∀ x ∈ (N.executableTree t maxDepth).closedProgram.values,
      (F.encoding.encode x).length ≤
        bitBound F (withUnit F coeff) (2 * (N.shape.vertices + N.shape.edges)) := by
  have hb := N.executableTree_bound t none (decode_withUnit_none F coeff) maxDepth bound htree
    (fun v x => family_bound F coeff (hf v x))
  exact ⟨hb.1.encoded_length_le F (withUnit F coeff),
    fun x hx => (hb.2 x hx).encoded_length_le F (withUnit F coeff)⟩

end Holant.Network
