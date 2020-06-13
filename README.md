# Why fork

First, these are all my solutions.

Second, I wanted a way to make it easier to do the tutorials without having to open new files each time and switch back and forth between my browser and VSCode. I created files for each section and appended the associated exercises using
```
cat ./unnamed_{start..end}.lean > section_name.lean
```
in bash (replaced start, end, & section_name with the actual values).

I then went through and modified import and variable statements, as well as renamed any variables depending on their context. I also copy/pasted all of the text between the code snippets from the original tutorial files into comments. Perhaps it would've been easier to just copy/paste the entire chapters and edited that way, but it's whatever.

## Original README.md text

### Mathematics in Lean

This tutorial depends on Lean, VS Code, and mathlib.
You can install them following the instructions
in the mathlib repository,
<https://github.com/leanprover-community/mathlib>.

To use this tutorial, you need to set up a project folder.
Open a terminal and type:
```
leanproject get mathematics_in_lean
```
Then open the project in VS Code:
```
code mathematics_in_lean
```
Once VS Code starts, open the file `welcome.lean`.
That will load the tutorial in a
separate window, and you are good to go.

### Contributing

PRs and issues should be opened at the upstream
[source repository](https://github.com/avigad/mathematics_in_lean_source).