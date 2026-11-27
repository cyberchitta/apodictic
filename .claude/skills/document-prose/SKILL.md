---
name: document-prose
description: What a finished page of prose about machine-checked proofs is, and how it is tested. For a document generated from a Lean project (Verso or similar) that explains its theorems to a general reader — short sentences, an argument stated at the grain of its lemmas with every conclusion grounded, one running example, a page that stands alone, and prose true of the Lean and of any text it formalizes; then the two fresh-agent reads that accept a page (a follow-the-page read on the rendered text alone, a cold read against the Lean and the sources) and the rules for every fix. Load before writing a new part of such a document, before changing any sentence of one, and before rewording a docstring the document shows. Ships the agent briefs and a page-text extractor. The repo supplies its own gate, vocabulary, markup and what is reserved to its owner.
---

# Document prose

A page of the document is finished when it has the properties below.
The writer cannot certify three of them, so two fresh agents test
them. The properties are the target. The reads are the acceptance
test. Everything else here serves those two.

Write to the properties from the first draft. Repairing a page
afterwards works, and costs more rounds.

This skill is the part that holds for any such document. It was
written from one repo's passes over eighteen pages, and has been used
in no other. The examples are that repo's. **Read the repo's own
document instructions with it**: the last section lists what they
supply.

## What a finished page is

**Sentences**

- One idea to a sentence. At most one subordinate clause. Few nouns.
- A premise of a theorem gets its own sentence or list item. Its Lean
  name follows in brackets, in the form the document already uses for
  that name.
- Lists, not chains of semicolons.
- One word has one sense on the page. Watch any term reused in a
  paragraph for two objects. (One page used "claim" both for a premise
  and for a lender's instrument; the second became "promise".)

**Argument**

- The conclusion comes first.
- The argument is stated at the grain of its lemmas. Each step gives
  its conclusion and the premises and earlier steps it rests on, with
  what each does there.
- Every conclusion names what it follows from. A "so", "only",
  "never" or "needs it" with no ground on the page is a defect,
  however short the sentence.
- Nothing narrates inside a lemma: no rewriting, unfolding, case
  splits, or which hypothesis feeds which argument. The Lean carries
  that.
- Each premise is given with what breaks it.
- The prose carries what the checker cannot: what the formal version
  forced into the open, such as a premise the proof never uses.

**Example**

- A theorem with more than a couple of premises is explained through
  one running example.
- The point of the example is stated.

**The page stands alone**

- A reader may land on any page. Every term is explained on the page
  before it is used, or pointed to.
- Terms the whole document uses are defined once, in one place. Any
  other page carries one line pointing there where it first needs
  them. No page repeats the definitions.
- A term or result explained in another part gets a link to that
  part, never a second explanation.

**True of the Lean**

- Every sentence about a definition or theorem says what the Lean
  says, no more and no less. Watch the quantifiers, which theorem
  carries which hypothesis, and one route against all routes.
- A "fails when" sentence is the exact negation of the condition.
- A counterfactual stays one: "would serve" is not "serves".
- A summary of a hypothesis is neither narrower nor broader than the
  hypothesis.
- No summary sentence asserts more than the theorem gives.

**True of the sources**, where the project formalizes a text

- Every quotation is verbatim and found in the edition before it is
  written down.
- A paraphrase keeps every qualifier, or the page quotes instead.
- The quotation stands beside the statement it is read as. Each place
  the encoding departs from the source is said.
- The running example is the source's own where it gives one.
  Anything the example needs and the source does not say is added and
  marked as the project's. What the source's example is silent on is
  worth saying: it is where the unstated premises are.
- A reading that is the project's says so.
- No sentence asserts a reading its owner has not approved: what a
  source means, implies or warrants, or why it says what it says.

## What the writer may not decide

Prose explains substance; it does not settle it. The repo's
instructions say what is reserved to its owner: typically what a
theorem assumes, how something is encoded, and how a source is read.
They also name any file a writer may not edit.

A sentence whose writing or fixing would change something reserved is
logged for the owner, stated so they can rule: the sentence, what the
change would assert, why it is a ruling. The page goes on with the
sentence as it is. A known error left pending a ruling is said to be
one in the record.

A rewrite leaves fixed every quotation, and whatever the repo's
instructions list as generated or checked (directives that pull in
docstrings, checked code blocks). Check those by script: the lists
before and after are identical.

## Writing a new part

Three habits make the first draft pass in fewer rounds.

1. Pick the running example before drafting.
2. Open the Lean definition or theorem, or the source passage, before
   writing the sentence about it.
3. List each theorem's premises from its signature, and write to that
   list.

Whoever drafts should hold the part's Lean in context, and should be
the one who later fixes the readers' flags. With an agent, that is one
agent, resumed by message. `briefs/writer.md` covers both jobs.

No part has yet been drafted from scratch under all of the above.
Expect fewer rounds than a repair needed, not none.

## The acceptance test

Both reads are by fresh agents. The writer's own read does not count:
the writer knows the proof, so the page always reads as followable.

1. **The repo's gate.** Builds, regenerated pages, and whatever checks
   the repo owns. It should also show which pages' visible text
   changed. That list must be the part's own page, plus any page that
   shows a changed docstring.
2. **Follow-the-page read** (`briefs/reader.md`). The reader gets one
   page's rendered text and nothing else. Make the text with
   `scripts/extract.sh <page.html>`, into a file outside the repo. The
   reader restates each step and flags what it cannot follow. The page
   passes when a second fresh reader, not shown the first one's flags,
   follows it end to end.
3. **Cold read** (`briefs/cold-read.md`). The reader gets the diff, the
   Lean and the sources. Each finding is MUST or OPTIONAL. MUST means a
   reader would come away believing something false, or the sentence
   asserts an unapproved reading. The page passes when a read finds no
   MUST.

The cold read is last. An error of fact outranks a residual
unclarity, and it reads the fixes the readers caused.

**Fix until both pass.** Flags go back to the writer, who classifies
each before fixing (the brief has the classes). Then the gate. Every
fix is itself read: a fresh cold read of just the changed hunks,
repeated until a read is clean. Two rounds of reader flags is the norm
for a repair.

A re-read's brief quotes the exact Lean lines and the source passage,
and the page text around each changed sentence. An elided brief
produces false MUSTs.

A re-read costs about the same whatever its size: the agent's start-up
dominates. So the saving is fewer rounds, and the next section is how.

The briefs carry `<PLACEHOLDERS>`. The main session fills each one
from the repo's instructions before sending.

## Rules for every fix

- Whoever writes a fix opens what it describes first. This binds the
  main session as much as an agent.
- A reader checks its own suggested replacement against the same
  evidence before suggesting it, and says so. Otherwise the suggestion
  is an unchecked fix.
- When a flag asks for the ground of a step, the ground comes only
  from the part's old text, another part, a docstring, or the Lean
  stated as what the Lean does. A ground that would be a new reading
  of a source is the owner's. A writer asked to ground a step will
  otherwise invent one.
- Splitting a sentence drops qualifiers ("alone", "only", "because",
  "strictly", "free") and moves clauses onto the wrong subject. After
  a split, check what "it", "this" and "so" now point at.
- An OPTIONAL point is taken only if a reader would otherwise come
  away believing something false. Each one taken buys a whole read.
  The rest is polish: listed for the part's next pass.
- An error that is repeated across parts is swept by every phrasing
  at once, not by the first phrase found.
- An error found in another part while working on this one goes into
  this part's commit and under its cold read.

## Mechanics

- **Serial.** One part at a time, where parts share a file, docstrings
  or a generated tree. Two readers on two pages may run at once, since
  they only read.
- **One commit a part**, once its last read is clean: the prose, the
  docstrings it touched, the regenerated pages.
- **Cost**, measured over one pass of eighteen repaired pages: four
  fresh agents a part, about 280k tokens. A new part's cost is not
  measured.

## Not settled

A change of a sentence or two to a finished page gets the cold read of
its hunk. Whether it also needs a new follow-the-page read has not
been decided. Until it is, give it one when a step of an argument was
added, removed or reordered.

## What the repo supplies

In its own instructions, not here:

- where the document is, how a part is delimited, and where a part's
  generated page is;
- the gate: the command, and what a passing run prints;
- the toolchain set-up an agent needs before a build;
- where the source editions are and how to search them;
- its fixed vocabulary, and wording rules that follow from its subject;
- the document's markup rules, and how one part links to another;
- where the common terms are defined;
- what a rewrite must leave unchanged;
- what is reserved to the owner, and any file a writer may not edit;
- the model page, which a writer reads before drafting;
- where the record goes: the line a part, the owner's items, the
  polish list;
- what a changed title breaks.
