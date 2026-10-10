import Holant.Proofs.Traversal.ArityTwo.ActionTableMeaning


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.WalkCodeExpansion
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open GraphPreprocessing FixedGadgetSubstitution.Compiler PortWalk Descriptors
open ActionTableMeaning
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s b : ℕ} {arity : ℕ → ℕ} {A : Type}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)

theorem terminal_expansion (hd : ∀ v, degree (arity := arity) r v ≤ 2)
    {p q : r.Ports arity} {xs : List (r.Ports arity)} (ht : Trace r h p xs (.terminal q)) :
    ∃ ms right,
      pathMatrices r h (vertex r h labels) (edge r h edges) xs = some (ms,right) ∧
      Traversal.Expands (rows r h labels edges codec (2*r.edges.length,[]))
        (Traversal.reference (address r h p))
        (MatrixEmission.word codec ([.literal (right true),.literal (right false)] ++ transferCode ms))
        xs.length := by
  generalize hs : Stop.terminal q = stop at ht
  induction ht with
  | repeated p => cases hs
  | terminal p ho =>
    have hp := terminal_unary r hd p ho
    refine ⟨[],unaryTable r (vertex r h labels) p.1,by simp [pathMatrices,hp],?_⟩
    have he := reference r h labels edges codec (2*r.edges.length,[]) p _ 0
      (by rw [body_terminal r h labels edges codec _ p hp]; exact Traversal.Expands.bits _ _)
    simpa [transferCode] using he
  | step p out xs stop ho ht ih =>
    obtain ⟨ms,right,hm,he⟩ := ih hs
    have hp := (other_some r p out ho).2.2
    let B := binaryTable r (vertex r h labels) p
    let E := edgeTable r h (edge r h edges) out
    refine ⟨B::E::ms,right,by simp [pathMatrices,hp,ho,hm,B,E],?_⟩
    have hc : address r h (cross r h out) ≠ 2*r.edges.length :=
      Nat.ne_of_lt (address_lt r h _)
    have hb := he.append (Traversal.Expands.bits
      (rows r h labels edges codec (2*r.edges.length,[]))
      (MatrixEmission.word codec (matrixStep E ++ matrixStep B)))
    have hr := reference r h labels edges codec (2*r.edges.length,[]) p _ xs.length
      (by simpa [body_binary r h labels edges codec _ p out ho,
        ActionTableCompiler.call,hc,B,E] using hb)
    simpa [transferCode,MatrixEmission.word,entries,List.flatMap_append,List.append_assoc,
      Nat.add_comm] using hr

theorem cycle_tail_expansion (root : r.Ports arity) (base : List Bool)
    {p : r.Ports arity} {xs : List (r.Ports arity)} (ht : Trace r h p xs (.repeated root))
    (hfresh : root ∉ xs) :
    ∃ ms, cycleMatrices r h (vertex r h labels) (edge r h edges) xs = some ms ∧
      Traversal.Expands (rows r h labels edges codec (address r h root,base))
        (ActionTableCompiler.call (address r h root,base) (address r h p))
        (base ++ MatrixEmission.word codec (transferCode ms)) xs.length := by
  generalize hs : Stop.repeated root = stop at ht
  induction ht with
  | terminal p ho => cases hs
  | repeated p =>
    cases hs
    exact ⟨[],rfl,by simpa [ActionTableCompiler.call,transferCode,MatrixEmission.word,entries]
      using Traversal.Expands.bits (rows r h labels edges codec (address r h root,base)) base⟩
  | step p out xs stop ho ht ih =>
    have hp : p ≠ root := by intro he; subst p; exact hfresh (by simp)
    have htail : root ∉ xs := fun hx => hfresh (by simp [hx])
    obtain ⟨ms,hm,he⟩ := ih htail hs
    let B := binaryTable r (vertex r h labels) p
    let E := edgeTable r h (edge r h edges) out
    refine ⟨B::E::ms,by simp [cycleMatrices,ho,hm,B,E],?_⟩
    have hb := he.append (Traversal.Expands.bits
      (rows r h labels edges codec (address r h root,base))
      (MatrixEmission.word codec (matrixStep E ++ matrixStep B)))
    have hr := reference r h labels edges codec (address r h root,base) p _ xs.length
      (by simpa [body_binary r h labels edges codec _ p out ho,B,E] using hb)
    have ha : address r h p ≠ address r h root := fun he => hp (address_injective r h he)
    simpa [ActionTableCompiler.call,ha,transferCode,MatrixEmission.word,entries,
      List.flatMap_append,List.append_assoc,Nat.add_comm] using hr

/-- The first vertex of a cycle is emitted once, including the self-loop case
where the recursive tail is empty and immediately supplies the basis word. -/
theorem cycle_start_expansion (root : r.Ports arity) (base : List Bool)
    (xs : List (r.Ports arity)) (ht : Trace r h root (root::xs) (.repeated root))
    (hfresh : root ∉ xs) :
    ∃ ms, cycleMatrices r h (vertex r h labels) (edge r h edges) (root::xs) = some ms ∧
      Traversal.Expands (rows r h labels edges codec (address r h root,base))
        (Traversal.reference (address r h root))
        (base ++ MatrixEmission.word codec (transferCode ms)) (root::xs).length := by
  cases ht with
  | step p out xs stop ho ht =>
    obtain ⟨ms,hm,he⟩ := cycle_tail_expansion r h labels edges codec root base ht hfresh
    let B := binaryTable r (vertex r h labels) root
    let E := edgeTable r h (edge r h edges) out
    refine ⟨B::E::ms,by simp [cycleMatrices,ho,hm,B,E],?_⟩
    have hb := he.append (Traversal.Expands.bits
      (rows r h labels edges codec (address r h root,base))
      (MatrixEmission.word codec (matrixStep E ++ matrixStep B)))
    have hr := reference r h labels edges codec (address r h root,base) root _ xs.length
      (by simpa [body_binary r h labels edges codec _ root out ho,B,E] using hb)
    simpa [transferCode,MatrixEmission.word,entries,List.flatMap_append,List.append_assoc,
      Nat.add_comm] using hr

theorem walk_length_ports (seen : List (r.Ports arity)) (p : r.Ports arity) :
    (walk r h (2*r.edges.length+1) seen p).1.length ≤ 2*r.edges.length := by
  have hn := walk_nodup r h (2*r.edges.length+1) seen p
  have hc : (walk r h (2*r.edges.length+1) seen p).1.length ≤ Fintype.card (r.Ports arity) := by
    rw [← List.toFinset_card_of_nodup hn]
    exact Finset.card_le_univ _
  have hp := r.ports_card_eq h
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hp
  omega

/-- Actual input is raw network bytes followed by its endpoint query. The
successful trace and the expander's fuel bound are both derived here. -/
theorem path_execution (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity) (hp : degree (arity := arity) r p.1 = 1) :
    ∃ ms right,
      pathMatrices r h (vertex r h labels) (edge r h edges)
        (walk r h (2*r.edges.length+1) [p] (cross r h p)).1 = some (ms,right) ∧
      ∃ time, time ≤ (ActionTableCompiler.timePolynomial s b arity labels edges codec false []).eval
          ((RawPortQuery.encoding s b arity).encode (query r h (cross r h p))).length ∧
        StackProtocol.RunsExactly (ActionTableCompiler.machine s b arity labels edges codec false []).computer.step
          (Turing.initList (ActionTableCompiler.machine s b arity labels edges codec false []).computer
            ((RawPortQuery.encoding s b arity).encode (query r h (cross r h p))))
          (Turing.haltList (ActionTableCompiler.machine s b arity labels edges codec false []).computer
            (MatrixEmission.word codec ([.literal (right true),.literal (right false)] ++ transferCode ms))) time := by
  obtain ⟨q,hq,_⟩ := (path_completion r h hd p hp).1
  have ht := walk_trace r h (2*r.edges.length+1) [p] (cross r h p) (walk_not_exhausted r h _ _)
  rw [hq] at ht
  obtain ⟨ms,right,hm,he⟩ := terminal_expansion r h labels edges codec hd ht
  refine ⟨ms,right,hm,?_⟩
  exact ActionTableCompiler.execute_expansion s b arity labels edges codec false []
    (query r h (cross r h p)) _ _ (by simpa [ActionTableCompiler.rows,
      ActionTableCompiler.queryContext,rows,address,query] using he)
    (walk_length_ports r h _ _)

/-- Closed traversal executes the proved first-return walk; in particular a
self-loop spends one row token and never recursively reads its initial row. -/
theorem cycle_execution (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1)
    (base : List Bool) :
    ∃ ms, cycleMatrices r h (vertex r h labels) (edge r h edges)
        (walk r h (2*r.edges.length+1) [] p).1 = some ms ∧
      ∃ time, time ≤ (ActionTableCompiler.timePolynomial s b arity labels edges codec true base).eval
          ((RawPortQuery.encoding s b arity).encode (query r h p)).length ∧
        StackProtocol.RunsExactly (ActionTableCompiler.machine s b arity labels edges codec true base).computer.step
          (Turing.initList (ActionTableCompiler.machine s b arity labels edges codec true base).computer
            ((RawPortQuery.encoding s b arity).encode (query r h p)))
          (Turing.haltList (ActionTableCompiler.machine s b arity labels edges codec true base).computer
            (base ++ MatrixEmission.word codec (transferCode ms))) time := by
  have hc := cycle_completion r h hd p hp hu
  obtain ⟨tail,hlist,_⟩ := cycle_cross_departures r h hd p hp hu
  have ht := walk_trace r h (2*r.edges.length+1) [] p (walk_not_exhausted r h [] p)
  rw [hc.1,hlist] at ht
  have hn := walk_nodup r h (2*r.edges.length+1) [] p
  rw [hlist] at hn
  obtain ⟨ms,hm,he⟩ := cycle_start_expansion r h labels edges codec p base tail ht
    (List.nodup_cons.mp hn).1
  refine ⟨ms,by simpa [hlist] using hm,?_⟩
  exact ActionTableCompiler.execute_expansion s b arity labels edges codec true base
    (query r h p) _ _ (by simpa [ActionTableCompiler.rows,
      ActionTableCompiler.queryContext,rows,address,query] using he)
    (by simpa [hlist, query] using walk_length_ports r h [] p)

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.WalkCodeExpansion
