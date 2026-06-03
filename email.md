Hi all (including Edward Hunter, who was forwarded another message I sent to DSAI a few days ago, as an FYI).

Great! Thank you for offering to meet. The best times for me would be

1. Tuesday 2:30pm or
2. Tuesday at 1pm,

but I can make any of the Tuesday times work. Could I invite a postdoc and PhD student to sit in on the call as well?

Let me describe the project in more detail and then attempt to answer your questions.

Firstly, this is part of a three-year grant aimed at producing AI generated formal proofs.

https://www.darpa.mil/research/programs/expmath-exponential-mathematics

Our specific team hopes to generate proofs in the computer proof assistant Agda, using the Agda-Unimath library (cofounded by my postdoc Egbert Rijke):

https://unimath.github.io/agda-unimath/

These proofs are written in an alternative formal system called "homotopy type theory" as described in the following books:

https://github.com/HoTT/book
https://arxiv.org/abs/2212.11082

(Note both of these websites include the LaTeX source files as well as compiled PDFs. Which format is easier for models to read?)

The broader project has two co-PIs who are both computer scientists: Yuriy Brun at UMass Amherst and Talia Ringer at UIUC. Our aim to ultimately build our own autoformalization agent. But the project I've written you about below is intended to be an experiment in agentic formal theorem proving that I expect to be successful based on some talks I attended at a conference two weeks ago:

https://arxiv.org/abs/2601.03298
https://types2026.cse.chalmers.se/abstracts/64.pdf

I'd like to run this experiment now because (i) if we don't, I expect someone else will and (ii) it will give us something to report at preliminary meetings with DARPA in early June and mid August, which may before my co-PIs have a working model to test.

As this is intended as a short term experiment, I'm happy to use a rather naive set-up, which I imagine might proceed along the following lines. (Note I am not an AI expert or a computer scientist, so please suggest improvements.)

1. I'd like to use codex, because I have a large credit balance donated by OpenAI to the expMath program. (Note this will be my first time using codex.)

2. I'd like to start with a natural language prompt asking codex to make a plan to formalize a specific result (the calculation of the 3rd homotopy group of the 2-sphere) as described in the Homotopy Type Theory book (the first link above) using the Agda-Unimath library. This calculation involves several preliminaries that have been formalized in other homotopy type theory libraries but are missing from Agda-Unimath. Our human expert team will review this plan and suggest improvements before we get to work.

3. We then plan to ask codex to get to work on the formalizations. Note there are existing MCP servers for Agda that I know nothing about:

https://libraries.io/npm/agda-mcp-server
https://github.com/faezs/agda-mcp

4. The plan is to have the formalization attempts supervised by a human expert team that will refine the prompting by teaching the model "agda unimath skills" in analogy with what has been done with other proof assistants: https://github.com/leanprover/skills

5. I'm hoping the end of this experiment will be
(i) a successful formalization, produced with humans in the loop, that we can then work on cleaning up to PR into the library
(ii) a thorough documentation of all the prompts, resource use, human interactions etc, for reporting purposes
(iii) the prototypical "agda unimath skills" that we can continue to refine and feed to other models, such as the one my co-PIs will develop in house.

If someone at DSAI would like to be involved throughout the whole experiment, that's great. In fact, I have some money in the year one budget that could go to an interested graduate student or researcher. But I'm also hoping that my team (myself, my postdoc, and my PhD student; all mathematicians) can learn enough in the initial consultation to continue from there.

Let me know attempt to answer your questions in line:

* Is the intended use case of the overall project to explore the feasibility of an end-to-end sandboxed environment for GenAI proof formalization, and this initial discussion is aiding in that exploration? Or is the goal to get assistance setting up some subset of the initial tooling under an effort in the bigger project? Or is it potentially both (or something totally different)?

Work by colleagues (cited above) suggests that our experiment is feasible and we can pivot to easier autoformalization targets if necessary. So I'm hoping to get assistance with the initial setup. An important aspect is that this will involve multiple human supervisors. I'm imaging this would be done through some sort of shared github repo.

* What would be some good outcomes for your overall project? Are publications the end goal, with the sandbox acting as an internal tool, or is the GenAI/sandbox pipeline the project product? Are there other outcomes we didn’t capture here?

It's likely the results will be for publication with the "agda unimath skills" part of the project product. But the broader project will be something more elaborate produced with my external collaborators that will be informed by this experiment.

* To be usable, does it need to have guaranteed performance metrics of some kind? Or can the process it creates be treated as a rough draft that will always have human interaction? Or is the usability measured in another way?

This is a rough draft with human interaction. I'd like to document performance metrics (and could use advice on how best to do so) but at this time we're not trying to optimize anything.

* Is the end goal of this request high-level feedback on an approach? Or is the vision that DSAI would participate in a shared effort of some sort?

As noted above, I think this can be successful if we just have some DSAI help getting started. But if someone there would like to be involved longer term, we're open to this as well.

* What is the library of formal proofs the team is using? Can you provide a link to it before the call?
 
Here is the library:

https://github.com/UniMath/agda-unimath

* Are there other input or output formats than latex?

The preferred output formal is something called lagda.md, which includes literate agda codeblocks within a markdown file. All of the library files have this format.

The natural language proofs currently exist in LaTeX or PDF, specifically in this chapter:
https://github.com/HoTT/book/blob/master/homotopy.tex

* What do the varying degrees of quality look like in the input examples? It seems like with formal proofs this would be strict, but we want to confirm.

I don't know exactly what you mean by this.

Thanks!
Emily