import Holant.Observability.Algebra

/-!
Finite ordered two-port chains with fixed actual binary inputs. The syntax
contains no linear combination, inverse, projective quotient, or arbitrary
matrix constructor. Only the complex span taken after evaluation is linear.
Series uses the existing genuine two-bit connection, with its right input
in inward port order. The native edge is always literal `X`.
-/

namespace Holant.Observability

noncomputable section

/-- Finite chain syntax; `atom i` refers to one fixed supplied actual binary.
`identity` and `exchange` are the explicit I and native-X links. -/
inductive Chain (ι : Type*) where
  | atom (i : ι)
  | identity
  | exchange
  | series (left right : Chain ι)
  | reverse (chain : Chain ι)

namespace Chain

variable {ι : Type*}

/-- Actual ordered physical kernel. The `join` definition sums the two
independent incident bits and retains all representative scalars. -/
def evaluate (family : ι → Mat) : Chain ι → Mat
  | .atom i => family i
  | .identity => Signature.equality
  | .exchange => Signature.disequality
  | .series left right => Kernel.join Signature.disequality
      (evaluate family left) (Kernel.transpose (evaluate family right))
  | .reverse chain => Kernel.transpose (evaluate family chain)

/-- The source's transfer convention is literal right multiplication by X. -/
def transfer (family : ι → Mat) (chain : Chain ι) : Mat :=
  Kernel.mul (evaluate family chain) Signature.disequality

@[simp] theorem evaluate_atom (family : ι → Mat) (i : ι) :
    evaluate family (.atom i) = family i := rfl

@[simp] theorem evaluate_identity (family : ι → Mat) :
    evaluate family .identity = Signature.equality := rfl

@[simp] theorem evaluate_exchange (family : ι → Mat) :
    evaluate family .exchange = Signature.disequality := rfl

@[simp] theorem evaluate_reverse (family : ι → Mat) (chain : Chain ι) :
    evaluate family (.reverse chain) = Kernel.transpose (evaluate family chain) := rfl

/-- Exact physical series composition, not an assumed algebra closure. -/
theorem evaluate_series (family : ι → Mat) (left right : Chain ι) :
    evaluate family (.series left right) =
      Kernel.mul (Kernel.mul (evaluate family left) Signature.disequality)
        (evaluate family right) := by
  simp only [evaluate, Kernel.join_eq_mul, Kernel.transpose_transpose]

@[simp] theorem transfer_exchange (family : ι → Mat) :
    transfer family .exchange = Signature.equality := by
  simp only [transfer, evaluate_exchange, Kernel.disequality_mul_disequality]

@[simp] theorem transfer_identity (family : ι → Mat) :
    transfer family .identity = Signature.disequality := by
  simp only [transfer, evaluate_identity, Kernel.equality_mul]

/-- Every transfer product is the transfer of another finite actual chain. -/
theorem transfer_series (family : ι → Mat) (left right : Chain ι) :
    transfer family (.series left right) =
      Kernel.mul (transfer family left) (transfer family right) := by
  simp only [transfer, evaluate_series, Kernel.mul_assoc]

/-- Port reversal acts on transfers by the source involution `X Tᵀ X`. -/
theorem transfer_reverse (family : ι → Mat) (chain : Chain ι) :
    transfer family (.reverse chain) =
      Kernel.mul (Kernel.mul Signature.disequality
        (Kernel.transpose (transfer family chain))) Signature.disequality := by
  simp only [transfer, evaluate_reverse, Kernel.transpose_mul,
    Kernel.transpose_disequality]
  rw [← Kernel.mul_assoc Signature.disequality Signature.disequality,
    Kernel.disequality_mul_disequality, Kernel.equality_mul]

/-- Transpose of a transfer is itself the transfer of a chain, using two
literal I links as well as physical port reversal. -/
theorem transfer_transpose (family : ι → Mat) (chain : Chain ι) :
    transfer family (.series .identity (.series (.reverse chain) .identity)) =
      Kernel.transpose (transfer family chain) := by
  simp only [transfer_series, transfer_identity, transfer_reverse]
  funext a b
  simp only [Kernel.disequality_mul, Kernel.mul_disequality, Bool.not_not]


/-- An explicit I edge is encoded by one literal I vertex between two
native X edges: `X I X = I`. The right chain remains in external order. -/
def equalitySeries (left right : Chain ι) : Chain ι :=
  .series left (.series .identity right)

/-- Exact orientation-aware equality-link composition, with a finite native
chain witness rather than an assumed equality-edge availability operation. -/
theorem evaluate_equalitySeries (family : ι → Mat) (left right : Chain ι) :
    evaluate family (equalitySeries left right) =
      Kernel.join Signature.equality (evaluate family left)
        (Kernel.transpose (evaluate family right)) := by
  simp only [equalitySeries, evaluate_series, evaluate_identity, Kernel.equality_mul,
    Kernel.join_eq_mul, Kernel.transpose_transpose, Kernel.mul_equality]
  rw [Kernel.mul_assoc, ← Kernel.mul_assoc Signature.disequality Signature.disequality,
    Kernel.disequality_mul_disequality, Kernel.equality_mul]

/-- Right multiplication by X is implemented by appending a literal I link. -/
theorem evaluate_append_identity (family : ι → Mat) (chain : Chain ι) :
    evaluate family (.series chain .identity) = transfer family chain := by
  rw [evaluate_series, evaluate_identity, Kernel.mul_equality]
  rfl

/-- The same operation undoes the transfer convention since X squared is I. -/
theorem transfer_append_identity (family : ι → Mat) (chain : Chain ι) :
    transfer family (.series chain .identity) = evaluate family chain := by
  rw [transfer, evaluate_append_identity, transfer, Kernel.mul_assoc,
    Kernel.disequality_mul_disequality, Kernel.mul_equality]

/-- Transfer relabelling does not enlarge the actual-chain set: both
inclusions have explicit finite-chain witnesses. -/
theorem transfer_range_eq_evaluate_range (family : ι → Mat) :
    Set.range (transfer family) = Set.range (evaluate family) := by
  ext A
  constructor
  · rintro ⟨chain, rfl⟩
    exact ⟨.series chain .identity, evaluate_append_identity family chain⟩
  · rintro ⟨chain, rfl⟩
    exact ⟨.series chain .identity, transfer_append_identity family chain⟩

end Chain

variable {ι : Type*}

/-- Exact source span: the complex span of actual finite-chain transfers. -/
def chainSpan (family : ι → Mat) : Submodule ℂ Mat :=
  Submodule.span ℂ (Set.range (Chain.transfer family))

theorem chain_transfer_mem (family : ι → Mat) (chain : Chain ι) :
    Chain.transfer family chain ∈ chainSpan family :=
  Submodule.subset_span ⟨chain, rfl⟩

@[simp] theorem chainSpan_equality_mem (family : ι → Mat) :
    (Signature.equality : Mat) ∈ chainSpan family := by
  simpa only [Chain.transfer_exchange] using chain_transfer_mem family .exchange

@[simp] theorem chainSpan_disequality_mem (family : ι → Mat) :
    (Signature.disequality : Mat) ∈ chainSpan family := by
  simpa only [Chain.transfer_identity] using chain_transfer_mem family .identity

/-- The fixed actual input appears without any projective normalization. -/
theorem atom_transfer_mem (family : ι → Mat) (i : ι) :
    Kernel.mul (family i) Signature.disequality ∈ chainSpan family :=
  chain_transfer_mem family (.atom i)

theorem kernel_mul_zero_left (A : Mat) : Kernel.mul 0 A = 0 := by
  funext a b
  simp [Kernel.mul_apply]

theorem kernel_mul_zero_right (A : Mat) : Kernel.mul A 0 = 0 := by
  funext a b
  simp [Kernel.mul_apply]

theorem kernel_mul_add_left (A B C : Mat) :
    Kernel.mul (A + B) C = Kernel.mul A C + Kernel.mul B C := by
  funext a b
  simp [Kernel.mul_apply]
  ring

theorem kernel_mul_add_right (A B C : Mat) :
    Kernel.mul A (B + C) = Kernel.mul A B + Kernel.mul A C := by
  funext a b
  simp [Kernel.mul_apply]
  ring

theorem kernel_mul_smul_left (c : ℂ) (A B : Mat) :
    Kernel.mul (c • A) B = c • Kernel.mul A B := by
  funext a b
  simp [Kernel.mul_apply]
  ring

theorem kernel_mul_smul_right (c : ℂ) (A B : Mat) :
    Kernel.mul A (c • B) = c • Kernel.mul A B := by
  funext a b
  simp [Kernel.mul_apply]
  ring

/-- Algebra closure follows from actual series composition and bilinearity;
it is not supplied as a premise of the source theorem. -/
theorem chainSpan_mul_mem (family : ι → Mat) (A : Mat) (hA : A ∈ chainSpan family)
    (B : Mat) (hB : B ∈ chainSpan family) : Kernel.mul A B ∈ chainSpan family := by
  induction hA, hB using Submodule.span_induction₂ with
  | mem_mem A B hA hB =>
    obtain ⟨left, rfl⟩ := hA
    obtain ⟨right, rfl⟩ := hB
    rw [← Chain.transfer_series]
    exact chain_transfer_mem family (.series left right)
  | zero_left B hB => simpa only [kernel_mul_zero_left] using (chainSpan family).zero_mem
  | zero_right A hA => simpa only [kernel_mul_zero_right] using (chainSpan family).zero_mem
  | add_left A B C hA hB hC hAC hBC =>
    rw [kernel_mul_add_left]
    exact (chainSpan family).add_mem hAC hBC
  | add_right A B C hA hB hC hAB hAC =>
    rw [kernel_mul_add_right]
    exact (chainSpan family).add_mem hAB hAC
  | smul_left c A B hA hB hAB =>
    rw [kernel_mul_smul_left]
    exact (chainSpan family).smul_mem c hAB
  | smul_right c A B hA hB hAB =>
    rw [kernel_mul_smul_right]
    exact (chainSpan family).smul_mem c hAB

/-- Transpose closure is likewise derived from finite chains, including the
two explicit I links needed to turn physical reversal into plain transpose. -/
theorem chainSpan_transpose_mem (family : ι → Mat) (A : Mat)
    (hA : A ∈ chainSpan family) : Kernel.transpose A ∈ chainSpan family := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨chain, rfl⟩ := hA
    rw [← Chain.transfer_transpose]
    exact chain_transfer_mem family _
  | zero => exact (chainSpan family).zero_mem
  | add A B hA hB htA htB => exact (chainSpan family).add_mem htA htB
  | smul c A hA htA => exact (chainSpan family).smul_mem c htA

/-- Source Theorem 5.17 for arbitrary supplied actual binary families.
In particular it applies to any chosen actual representatives of a retained
normalized set. No completeness, finiteness, or invertibility assumption is
needed for this stronger algebraic assertion. -/
theorem realizable_binary_kernel_span (family : ι → Mat) :
    chainSpan family = ixSpan ∨ chainSpan family = ⊤ :=
  transpose_stable_algebra_dichotomy (chainSpan family)
    (chainSpan_equality_mem family) (chainSpan_disequality_mem family)
    (chainSpan_mul_mem family) (chainSpan_transpose_mem family)

/-- The two conclusions of the source theorem, with an actual-chain definition
of the span and the exact bilinear Frobenius complement. -/
theorem dressed_kernel_observability (family : ι → Mat) :
    (chainSpan family = ixSpan ∨ chainSpan family = ⊤) ∧
    frobeniusOrthogonal ixSpan = {A | ∃ u v : ℂ, A = invisible u v} :=
  ⟨realizable_binary_kernel_span family, ixSpan_frobenius_complement⟩

end
end Holant.Observability
