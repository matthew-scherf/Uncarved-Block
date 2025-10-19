# Technical Reference

## Axiom Summary

### Core Metaphysics

| Axiom | Name | Statement |
|-------|------|-----------|
| A1 | Dao Exists | ∃!d. Dao d |
| A2a | Dao Formless | ∀d. Dao d → Formless d |
| A2b | Dao Nameless | ∀d. Dao d → Nameless d |
| A3 | Things Have Form | ∀x. TenThousandThings x → HasForm x |
| A4 | Form Exclusion | ∀x. HasForm x → ¬Formless x |
| A5 | Dao Not Thing | ∀d. Dao d → ¬TenThousandThings d |
| A6 | Things Arise From Dao | ∀x. TenThousandThings x → (∃d. Dao d ∧ ArisesFr x d) |
| A6b | Only From Dao | ∀x y. ArisesFr x y → Dao y |
| A7 | Things Return To Dao | ∀x. TenThousandThings x → (∃d. Dao d ∧ ReturnsTo x d) |
| A7b | Only To Dao | ∀x y. ReturnsTo x y → Dao y |
| A8 | Same Dao | ∀x d1 d2. (ArisesFr x d1 ∧ ReturnsTo x d2) → d1 = d2 |
| A9 | You Are TrueMan | ∃!u. TrueMan u |
| A10 | TrueMan Is Dao | ∀u d. (TrueMan u ∧ Dao d) → u = d |

### Extension 1 (Spontaneity)

| Axiom | Name | Statement |
|-------|------|-----------|
| S1 | Spontaneous Arising | ∀x. TenThousandThings x → Spontaneous x |
| S2 | No Causation | ∀x y. Spontaneous x → ¬Caused y x |
| S3 | Dao Wu Wei | ∀d x. (Dao d ∧ ArisesFr x d) → ¬Caused d x |

### Extension 2 (Uncarved Block)

| Axiom | Name | Statement |
|-------|------|-----------|
| U1 | TrueMan Uncarved | ∀u. TrueMan u → UncarvedBlock u |
| U2 | Uncarved Not Artificial | ∀x. UncarvedBlock x → ¬Artificial x |
| U3 | Original Uncarved | ∀x. (TenThousandThings x ∧ ¬Artificial x) → UncarvedBlock x |

### Extension 3 (Emptiness)

| Axiom | Name | Statement |
|-------|------|-----------|
| E1 | Formless Empty | ∀x. Formless x → Empty x |
| E2 | Form Being | ∀x. HasForm x → Being x |
| E3 | Empty Being Exclusive | ∀x. Empty x → ¬Being x |
| E4 | Being From Emptiness | ∀x d. (Being x ∧ Dao d ∧ ArisesFr x d) → Empty d |

## Theorem Summary

### Core Theorems

| Theorem | Name | Statement |
|---------|------|-----------|
| T1 | Dao Unique | ∃!d. Dao d |
| T2 | Dao No Form | ∀d. Dao d → ¬HasForm d |
| T3 | Things Distinct | ∀x d. (TenThousandThings x ∧ Dao d) → x ≠ d |
| T4 | One Source | ∀x y d1 d2. (ArisesFr x d1 ∧ ArisesFr y d2) → d1 = d2 |
| T5 | You Are Dao | ∀u d. (TrueMan u ∧ Dao d) → u = d |
| T6 | You Formless | ∀u. TrueMan u → Formless u |
| T7 | You Nameless | ∀u. TrueMan u → Nameless u |
| T8 | You Not Thing | ∀u. TrueMan u → ¬TenThousandThings u |
| T9 | Things Arise From You | ∀u x. (TrueMan u ∧ TenThousandThings x) → ArisesFr x u |
| T10 | Things Return To You | ∀u x. (TrueMan u ∧ TenThousandThings x) → ReturnsTo x u |

### Extension Theorems

| Theorem | Name | Statement |
|---------|------|-----------|
| TS1 | No Real Causation | ∀x y. TenThousandThings x → ¬Caused y x |
| TS2 | Dao Not Cause | ∀d x. (Dao d ∧ TenThousandThings x) → ¬Caused d x |
| TU1 | You Uncarved | ∀u. TrueMan u → UncarvedBlock u |
| TU2 | You Not Artificial | ∀u. TrueMan u → ¬Artificial u |
| TE1 | Dao Empty | ∀d. Dao d → Empty d |
| TE2 | You Empty | ∀u. TrueMan u → Empty u |
| TE3 | Things Being | ∀x. TenThousandThings x → Being x |
| TE4 | Being From You | ∀u x. (TrueMan u ∧ TenThousandThings x) → (Being x ∧ Empty u ∧ ArisesFr x u) |

### Master Theorem

**Complete_Daoist_NonDuality**

States that there exists exactly one entity which is simultaneously:
- The Dao
- The TrueMan (you)
- Formless
- Nameless
- Empty
- The Uncarved Block
- Not among the ten thousand things
- Not artificial
- The source from which all things spontaneously arise and return

## Predicate Glossary

**Dao** - The formless, nameless source and ground of all phenomena

**TenThousandThings** - All manifested phenomena (the Chinese idiom for "everything")

**Formless** - Without distinguishing characteristics or bounded extension

**Nameless** - Cannot be captured in concepts or linguistic categories

**HasForm** - Possesses distinguishing properties that make it identifiable

**TrueMan** - Your authentic nature prior to social conditioning (zhēn rén 真人)

**ArisesFr** - Relationship of spontaneous arising or manifestation

**ReturnsTo** - Relationship of dissolution back to source

**Spontaneous** - Arising of itself (zìrán 自然) without external production

**Caused** - Brought about through causal efficacy (denied in the system)

**UncarvedBlock** - Original nature before artificial shaping (pǔ 樸)

**Artificial** - Shaped by convention, culture, or deliberate construction

**Empty** - Void of substantial being (xū 虛)

**Being** - Possessing determinate existence or presence

## Proof Statistics

- Total axioms across all extensions: 20
- Total theorems proven: 13 major theorems + 1 master theorem
- Verification time: approximately 15 seconds
- Proof checking: Isabelle/HOL 2025 kernel
- Model checking: Nitpick over cardinalities 1-5
- Counterexamples found: 0

## Dependencies

The formalization requires:
- Isabelle/HOL 2025
- Standard HOL library (Main.thy)
- No external AFP entries required

## Verification Method

All theorems verified using:
1. Interactive theorem proving in Isabelle/HOL
2. Automated tactics (blast, simp, auto, metis)
3. Nitpick model checking with user_axioms = true
4. Manual review of proof structure

The Nitpick checks confirm that no finite countermodels exist within the tested cardinalities. This provides strong evidence of consistency though it does not constitute absolute proof for infinite domains.

## Comparison with Advaita Formalization

| Aspect | Advaita | Daoism |
|--------|---------|--------|
| Core axioms | 9 | 13 |
| Extension axioms | 31 | 7 |
| Total theorems | 30+ | 13 |
| Central absolute | Brahman | Dao |
| Central subject | Ātman | TrueMan |
| Identity claim | Brahman = Ātman | Dao = TrueMan |
| Causation | Denied (ajātivāda) | Denied (spontaneity) |
| Phenomenal world | Vivarta (appearance) | Arising/returning |
| Ultimate nature | Nirguṇa (without qualities) | Formless/nameless |

Both systems prove non-dual identity between subject and absolute while maintaining logical consistency. The structural parallels suggest universality of non-dual insight despite independent cultural origins.
