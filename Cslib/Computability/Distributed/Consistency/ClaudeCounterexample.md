# Question:

I think that the last part of Proposition 5.1 on page 61 of the book, that BasicEventualConsistency implies QuiescentConsistency, is false.  I already know that its proof doesn't work, but that doesn't necessarily mean that the statement is false.  Can you come up with an explicit counterexample?

# Answer:

Yes, the statement is false. The proof breaks at the step "for each update event u, there exists a finite set E′ᵤ such that u is visible for all events in [f] \ E′ᵤ (by EventualVisibility)". EventualVisibility only constrains events that u *returns before*. An update that is rb-before nothing has no visibility obligations at all, and the definition of a well-formed history does not rule that out.

**Counterexample.** Take the register F = F_reg (with initial value undef), and events

  E = {w} ∪ {r₀, r₁, r₂, …}

with:

- **Operations and return values:** op(w) = wr(1) with rval(w) = ok, and op(rₙ) = rd with rval(rₙ) = 1 if n is odd and undef if n is even.
- **Sessions:** two sessions, {w} and {r₀, r₁, …}.
- **Returns-before:** rb = {(rₘ, rₙ) | m < n}. In particular, w is rb-unrelated to every other event.
- **Visibility:** vis = {(rₘ, rₙ) | m < n} ∪ {(w, rₙ) | n odd}.
- **Arbitration:** ar is any total order, e.g. w < r₀ < r₁ < ⋯.

So the read session alternates forever between seeing and not seeing the write.

**It is a well-formed history.** (h5) holds because the only rb-predecessors are reads, which return. (h6) holds because rb is a chain, hence an interval order. (h7) holds because each session's rb is an enumeration (trivially for {w}, and the order of ℕ for the reads). rb is natural.

**It satisfies BasicEventualConsistency(F_reg).**

- *Abstract execution conditions.* vis is acyclic and natural, since rₙ has at most n + 1 predecessors. ar is total.
- *EventualVisibility.* For e = w, the set {e′ | w →rb e′ ∧ ¬(w →vis e′)} is empty, because w is rb-before nothing. For e = rₘ, every later read sees rₘ, and rₘ is not rb-before w.
- *NoCircularCausality.* so ∪ vis consists only of edges w → rₙ and rₘ → rₙ with m < n, so hb is acyclic.
- *RVal(F_reg).* Reads don't change the register state, so F_reg(rd, C) is 1 if w ∈ C and undef otherwise. Now context(rₙ) contains w exactly when n is odd, which matches rval(rₙ). Also, context(w) = ∅ and F_reg(wr(1), ∅) = ok = rval(w).

**It violates QuiescentConsistency(F_reg).** rd ∈ readonlyops(F_reg), since removing a read from any context changes no return value. So the set of non-read-only events is {w}, which is finite, and the premise holds. But for any context C, F_reg(rd, C) is a single value, while the read session returns 1 and undef each infinitely often. So infinitely many events in that session disagree with F(op(e), C).

**Remarks.**

1. **Realizing this on a timeline.** Since rval(w) = ok, w's interval must end at some finite time. It overlaps all the reads, so the infinitely many reads have to happen in bounded time (Zeno behavior). The formal definition of histories, and hence Proposition 5.1 as stated "for all histories H ∈ H", doesn't exclude this.
2. **Why the write can't simply be pending.** You might try to make w a pending operation (rval = ∇) instead, but that doesn't work. RVal forbids ∇ for non-blocking operations like wr; the book makes this point on p. 92 about reads.
3. **Why the gap is essentially the only one.** Suppose you add the assumption that every event with rval ≠ ∇ is rb-before all but finitely many events of each session. Then, in histories whose non-read-only events are all complete (as they must be for non-blocking types under RVal), the book's argument goes through: each of the finitely many updates is visible to almost all events of each session, and claim 1 strips away the read-only events. So a non-Zeno/fairness condition of this kind is what's missing.
