# Enrichment Review: InjectiveWorld

## Ranked Suggestions

### 1. Concrete counterexample level for "Injective(g ∘ f) does NOT imply Injective g"

**What**: Add a level where the player constructs a concrete counterexample proving `¬ (∀ (g : β → γ) (f : α → β), Injective (g ∘ f) → Injective g)` or a specific instance with `g` non-injective but `g ∘ f` injective.

**Why**: L05's conclusion states this is false and gives a hand-wavy example ("f : Fin 1 → Fin 2 and g : Fin 2 → Fin 1"), but the player never proves it. L03 already teaches the proof shape for disproving injectivity of a single function. This is the natural companion: disproving a universal claim about composition. The asymmetry between "extracting f" (true) and "extracting g" (false) is one of the world's most important ideas, and it is currently only stated, not proved. Stating a mathematical fact without proving it is the definition of a missed teaching moment in a proof game.

**Where**: New level between L05 and L06 (or after L05 as L05b). The current L05 conclusion already sets it up.

**Effort**: High (new level).

**Recommend**: Yes — this is the single most important improvement. A claim that goes unproved undermines the world's pedagogical integrity.

---

### 2. `congrArg` as a required proof move (not just a footnote)

**What**: Add a level or modify L05 to require the player to use `congrArg g hab` (or an equivalent "apply g to both sides" step) as the primary proof technique rather than the `show` + `rw` workaround.

**Why**: L05's conclusion introduces `congrArg` as an "alternative" and says "you will see `congrArg` used throughout the course." But the player never actually uses it — it's a Branch alternative, not the main path. If this proof move is important enough to foreshadow, it's important enough to require. The principle "applying a function to both sides of an equation" is a foundational mathematical skill that deserves its own moment.

**Where**: L05 (modify the primary proof path) or add a short coaching level after L05 dedicated to `congrArg`.

**Effort**: Medium (modify L05's main path and hints) or High (new coaching level).

**Recommend**: Yes — a proof move described as recurring deserves to be taught, not footnoted.

---

### 3. Concrete composition instantiation

**What**: Add a level where the player proves injectivity of a concrete composed function (e.g., `fun n : ℕ => 2 * (n + 1)`) by decomposing it as `doubling ∘ successor` and applying the composition theorem from L04.

**Why**: L01–L02 prove injectivity of concrete functions directly. L04 proves composition abstractly. But no level connects these: "here are two concrete injective functions; now use the composition theorem to conclude their composition is injective." This is the natural bridge between the concrete and abstract halves of the world. Without it, a player may not see how the abstract composition result applies to real functions.

**Where**: New level after L04 (between current L04 and L05).

**Effort**: High (new level).

**Recommend**: Consider — valuable for grounding, but the boss (L08) partially fills this role with its semi-concrete setup.

---

### 4. Acknowledge the `injection` tactic's existence

**What**: Add a sentence to L01's conclusion (or the world introduction) noting that Lean has a built-in `injection` tactic for constructor injectivity, and that it is deliberately disabled here so the player learns the general proof shape.

**Why**: `injection` is disabled in L01, L02, and L08. A player who knows about `injection` (or discovers it) will wonder why it doesn't work. A player who doesn't know about it misses learning that it exists. One sentence ("Lean has an `injection` tactic that handles constructor-based injectivity automatically — we disable it here so you learn the universal proof shape") is honest, educational, and costs nothing.

**Where**: L01 conclusion.

**Effort**: Low (one sentence in an existing conclusion).

**Recommend**: Yes — costs nothing, prevents confusion, teaches a real Lean feature.

---

### 5. Name the "peeling" strategy explicitly

**What**: In L04's conclusion, name the `apply hf; apply hg; exact hab` pattern as the "peeling" or "layer-stripping" strategy for composition proofs.

**Why**: The conclusion describes the pattern well but doesn't give it a name. L08's introduction references "chain `apply` through two injectivity hypotheses" but there's no consistent label. Named strategies are more memorable and transferable. The SurjectiveWorld will use a dual pattern (witness chaining), and having a named contrast ("peeling for injectivity, chaining for surjectivity") strengthens both worlds.

**Where**: L04 conclusion (modify existing text).

**Effort**: Low (a few words in an existing conclusion).

**Recommend**: Consider — helpful for cross-world vocabulary, but borderline between enrichment and editorial polish.

---

### 6. The "left-cancellation" characterization of injectivity

**What**: Mention (in a conclusion or introduction) that injectivity is equivalent to left-cancellability: `Injective f ↔ ∀ g₁ g₂, f ∘ g₁ = f ∘ g₂ → g₁ = g₂`. Optionally, add a level proving one direction.

**Why**: This is a fundamental characterization that connects the element-level definition (`f a = f b → a = b`) to the function-level property (left-cancellable). It reframes injectivity in terms the player has already practiced (composition), creating a satisfying conceptual closure. The → direction is provable with the techniques already taught in this world.

**Where**: New level before the boss, or a mention in the world conclusion.

**Effort**: High (new level) or Low (mention in conclusion).

**Recommend**: Consider — mathematically significant but may exceed the world's scope. A brief mention in L08's conclusion ("Injectivity can also be characterized as left-cancellability of f under composition — you will encounter this in later courses") costs nothing.

---

### 7. Why injectivity matters: one concrete motivation

**What**: Add a sentence or two to the world introduction connecting injectivity to a familiar concept: encoding (an injective encoding is decodable), unique identifiers (student IDs, social security numbers), or the pigeonhole principle (a non-injective function on a finite set must "collide").

**Why**: The world introduction defines injectivity as "preserves distinctness" and "never collapses information," which is mathematically precise but may feel abstract. One concrete sentence ("Think of a student ID system: it must be injective — two different students must get different IDs, or the system fails") makes the definition stick.

**Where**: World introduction (modify existing text).

**Effort**: Low (one sentence).

**Recommend**: Consider — good for motivation, but the world introduction is already quite good and the information-loss angle in L03 partially covers this.

---

## Overall Impression

InjectiveWorld is a well-structured world with a clear pedagogical arc: concrete proofs (L01–L02), counterexample (L03), abstract composition (L04–L05), coaching interlude (L06), left inverses (L07), and integration boss (L08). The conclusions are unusually strong — they articulate proof shapes, name alternatives, and foreshadow future worlds. The addition of L06 as a standalone rewriting coaching level before L07 is particularly good pedagogy.

The single most important improvement is **adding a counterexample level for the false converse "Injective(g ∘ f) → Injective g."** The world makes this claim in prose but never proves it, which is a missed teaching moment and contradicts the world's own pattern of proving non-injectivity (L03). A proof game that tells you something is false without letting you prove it is leaving its best material on the table.
