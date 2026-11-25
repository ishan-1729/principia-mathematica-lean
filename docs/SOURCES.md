# Sources and copyright

## The text
- Alfred North Whitehead and Bertrand Russell, *Principia Mathematica*, **Volume I**. Cambridge University Press, 1910. Preface, Introduction (Chapters I–III), Part I (*Mathematical Logic*, ✱1–✱43) and Part II (*Prolegomena to Cardinal Arithmetic*, ✱50–✱97), with the Errata.
- Alfred North Whitehead and Bertrand Russell, *Principia Mathematica*, **Volume II**. Cambridge University Press, 1912. Prefatory Statement of Symbolic Conventions, Part III (*Cardinal Arithmetic*, ✱100–✱126), Part IV (*Relation-Arithmetic*, ✱150–✱186) and Part V (*Series*, ✱200–✱234, Sections A–C), with the Additional Errata to Volume I and the Errata to Volume II.
- Both title pages are those of the first edition: "Cambridge at the University Press 1910" and "1912". The second edition (1925–1927) is not used. Its new Introduction and Appendices are not formalized.

### Digital editions
- **Project Gutenberg eBook #78050**: *Principia Mathematica*, Volume I.
  - Catalogue page: <https://www.gutenberg.org/ebooks/78050>
- **Project Gutenberg eBook #78255**: *Principia Mathematica*, Volume II.
  - Catalogue page: <https://www.gutenberg.org/ebooks/78255>

The release dates and the producers' credits are given on the catalogue pages. The source files used here (below) do not carry Project Gutenberg's header, so they are not repeated here.

**Source used here:** the MathJax HTML source of each eBook, `78050-src.htm` and `78255-src.htm`. Mathematics is TeX between `\( … \)` and `\[ … \]`. The files are not part of this repository; `scripts/extract_source.py` takes their paths as arguments.

**Transcriber's notes.** Both files end with transcriber's notes. In summary:
- the items in the Errata of all three volumes have been applied to the text;
- an abbreviated citation such as "✱2·37·38" stands for ✱2·37 and ✱2·38;
- some propositions cited by the authors are not stated in the text: ✱84·44 (Vol. I, p. 326); ✱113·01, ✱120·450, ✱122·436, ✱122·473, ✱126·122, ✱124·62, ✱151·45 and ✱165·372 (Vol. II);
- from Section C on, a lower-case `a` is a limit and a Greek `α` is a class (Volume II);
- the alt texts of the figures of Volume II are the post-processor's.

The e-text applies most errata to the statements, but not all. The Lean files record, proposition by proposition, where an erratum is already in the e-text, where it had to be applied, and where the e-text has a transcription error of its own (`PrincipiaMathematica/Basic.lean`, §9).

## Volume III
- Alfred North Whitehead and Bertrand Russell, *Principia Mathematica*, **Volume III**. Cambridge University Press, 1913. The rest of Part V (*Series*: well-ordered series, finite and infinite series and ordinals, compact series, rational series and continuous series) and Part VI (*Quantity*).
- It is not yet on Project Gutenberg. At the time of writing it is being proofread at Distributed Proofreaders (<https://www.pgdp.net>). It will be extracted and formalized in the same way once its Gutenberg edition is published.

## Copyright status
| Jurisdiction | Rule | Status |
|---|---|---|
| United States | published before 1931 | public domain (Volume I published 1910, Volume II 1912) |
| India | author's life + 60 years | Whitehead d. 1947, Russell d. 1970: public domain from 1 January 2031 |
| EU / UK | author's life + 70 years | public domain from 1 January 2041 |

The project uses the text under the US status. Users elsewhere should check the law of their own country before reusing the quotations.

**How the text is used:**
- Quotations in the Lean files and in `data/principia.json` reproduce the 1910 and 1912 text, as transcribed in the Project Gutenberg e-texts.
- None of the Project Gutenberg licence boilerplate or trademark is reproduced.

## How the quotations were produced
`scripts/extract_source.py` reads the two HTML files and writes `data/principia.json`. Usage:

```sh
python3 scripts/extract_source.py path/to/78050-src.htm path/to/78255-src.htm
```

For each volume it records:
- the front matter and the explanatory texts (Preface, Introduction, Prefatory Statement, Summaries of Parts and Sections, Notes, Errata), as text;
- each starred number ✱N: its Part and Section, its title, its original page, and its summary (the prose before the first proposition);
- each numbered proposition ✱N·M: the formula as printed (with its list of references), its kind (`Pp`, primitive proposition; `Df`, definition; otherwise an asserted proposition), its original page, and the text that follows it up to the next proposition (the demonstration and any comment).

The result has 63 numbers and 3454 propositions in Volume I, and 72 numbers and 3901 propositions in Volume II: 7355 in all.

Clean-up applied:
- HTML tags are removed. Italics become `*…*`.
- Footnotes are inlined as `[Note: …]`.
- Mathematics stays as MathJax TeX.
- Where the summary of a number repeats a proposition before the body, the proposition is recorded once, from the body.
- A proposition is a paragraph headed by its number. Most are printed `*N·M.` in bold; the few printed otherwise (a full stop or a star for the centred dot, no star, no bold, a space at the full stop) are recorded as well. Seven printed with a wrong number are listed in a table in the script: four with another starred number's number (✱93·12, ✱93·2, ✱96·31, ✱214·11), and three with another proposition's number (✱116·331 printed `*116·311`, ✱117·281 printed `*117·2`, ✱201·62 printed `*201·26`). The first two numbers are also printed for their own propositions, ✱116·311 and ✱117·2, so the table entry for each applies only to the print whose formula it names.

`scripts/make_skeletons.py` turns `data/principia.json` into the Section files: one unit block `## [✱N] Title` per number, quoting the opening of its summary, and one docstring per proposition, with its number and its formula as printed. `scripts/prop_table.py` checks that every proposition of `data/principia.json` has its declaration `pmN_M`, and writes `docs/PROPOSITIONS.md`.
