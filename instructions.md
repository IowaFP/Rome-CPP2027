# Author Instructions for Camera-Ready Articles
	
## Action Items

- Exhaustively consider reviewer comments. Make sure you have done your best to address the comments in the reviews of your paper.
- Submit the publishing-rights to the publisher via the online publishing-rights system. The link can be found on the submission page.
- For conferences/workshops: Register at least one author for attending the event.
- Please submit your paper by the deadline specified in your acceptance-notification e-mail.

## General Formatting

Make sure your paper:

- [x] is based on the most recent version of the formatting template/style (see details below),
- [x] does not change any style or formatting settings of the template,
- [x] does not exceed the page limit specified in the acceptance-notification e-mail,
- [x] is in PDF format,
- [x] has all fonts embedded in the PDF file,
- [x] uses only scalable font types (like Type 1, TrueType) --- bit-mapped font types (like Type 3) are not acceptable,
- [x] does not have page numbers or footers,
- [x] is in letter page size,
- [x] provides the affiliation (institution and country) in the author information on the first page,
- [x] defines all authors individually (not as a list),
- [x] has the title and all headings properly capitalized,
- [x] does not use footnotes and references in the abstract,
- [x] provides a DOI for each item in the References section (if possible),
- [x] has all diagrams embedded in vector graphics
- [x] (if not possible, use a high-resolution bitmap format of at least 300 dpi; do not use JPG, but a lossless format like PNG or GIF; JPG is ok for photos),
- [x] has all text in figures and tables large enough and readable when printed,
- [x] has a caption for every figure or table,
- [x] has all units consistently separated from their values with a half space (e.g., '\SI{33}{GB}'),
- [x] has balanced columns on the last page, if the page is not filled,
- [x] uses the microtype package using \usepackage{microtype} for improved typesetting,
- [x] has no orphans and widows,
- [x] has reduced the use of bold face and bright colors in the text as much as possible, underlining is not used at all in the text,
- [x] has all third-party material appropriately attributed (mention author, copyright holder, and origin).

General help and more detailed advice on formatting papers can be found on our Help page.

# Conference/Publisher-Specific Requirements

The format of your paper must strictly adhere to the ACM Format.
LaTeX: Use version acmart v2.21 or newer.
You can directly download the LaTeX class file acmart and the BibTeX ACM Reference Format, which are also available from CTAN.

## LaTeX blurbs

Please use the 'sigplan' style by using the following LaTeX class configuration:

```
\documentclass[sigplan,screen]{acmart}
```        

If you typeset your bibliography with biblatex instead of BibTeX, then add the option natbib=false to the document class, as the acmart documentation requires:

```
\documentclass[natbib=false,sigplan,screen]{acmart}
```


Article Setup: Copy the following code into your LaTeX document before \begin{document}.
Please note that this is specific to your paper (Word users, please insert the information in the appropriate fields).
Please use a new line for each of these commands.

```
%%% The following is specific to CPP '27 and the paper
%%% 'Normalization by Evaluation of Higher-Order Rows'
%%% by Alexander Hubers and J. Garrett Morris.
%%%
\setcopyright{cc}
\setcctype{by-nc-nd}
\acmDOI{10.1145/3871849.3871874}
\acmYear{2027}
\copyrightyear{2027}
\acmISBN{979-8-4007-3146-4/2027/01}
\acmConference[CPP '27]{Proceedings of the 16th ACM SIGPLAN International Conference on Certified Programs and Proofs}{January 11--12, 2027}{Mexico City, Mexico}
\acmBooktitle{Proceedings of the 16th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP '27), January 11--12, 2027, Mexico City, Mexico}
\acmSubmissionID{poplws27cppmain-p14-p}
\received{2026-09-10}
\received[accepted]{2026-11-10}
```

Then, please copy the following code into your LaTeX document after \begin{document}.
If you use umlauts or other unicode characters, please do not forget to add \usepackage[utf8]{inputenc} to the preamble of your LaTeX document.
Please re-add linebreaks to the title and a short title if necessary.

```
\title{Normalization by Evaluation of Higher-Order Rows}

\author{Alex Hubers}
\correspondingauthor
\orcid{0000-0002-6237-3326}
\affiliation{%
  \institution{University of Iowa}
  \department{Computational Logic Center, Department of Computer Science}
  \city{Iowa City}
  \country{USA}
}
\email{alexander-hubers@uiowa.edu}

\author{J. Garrett Morris}
\orcid{0000-0002-3992-1080}
\affiliation{%
  \institution{University of Iowa}
  \city{Iowa City}
  \country{USA}
}
\email{garrett-morris@uiowa.edu}
```


## CCS Nonsense

The ACM style provides the three small sections 'CCS Concepts', 'Keywords', and 'ACM Reference Format' to follow the abstract; these are mandatory on the paper in the given order. Make sure you correctly classify your paper using the 2012 ACM Computing Classification System (CCS). The content of the CCS has to be picked from the provided list (with the CCS tool). The order of the CCS concepts is based on their relevance. The keywords are user-defined. (You should also insert the CCS XML snippet into your sources: for LaTeX documents using the environment 'CCSXML' and for Word documents using the properties dialog.)

During the submission of the camera-ready paper using our submission site, you need to copy the XML snippet from the ACM CCS tool into a text field of the submission form.
Information in running heads:
- Authors: Use the complete list of authors as long as it fits on one line in the running heads. In other words, first try to use the full author information. If it is longer than one line, initial the given names (and use the command \shortauthors to declare the short version of the author list), if still longer than one line, use only surnames, and only as a last resort, use et al. after the first author.
- Title: The title should not use more than one line in the running heads (starting on page 3). If the title is too long to fit on one line, please use the beginning of the title (delete from the end), followed by ellipsis ("...") (specifying the shorter title using brackets as option argument for the \title command). Please note that a short title that concisely describes the contribution is always a good idea.
- Acknowledgements such as "This work was partially funded by ..." should either go to the acknowledgements section or be formatted using the command \titlenote, but not as \thanks, in the ACM style acmart.

## Final Checklist

Before submitting your paper as camera-ready, please check off the following items (this is not a complete list and does not replace the ACM style guide, but serves as a list of frequently noticed issues):

- [x] The text height must not exceed 23.5 cm. The text width must not exceed 18 cm.
- [x] Text, tables, and figures (also headings, program code, and formulas) must not run into the margins outside the text area and between the columns.
- [x] The font size is 10 pt for all body text, including classification, ACM Reference format, and acknowledgments. The font size of the references can be from 8 pt to 10 pt.
- [x] The title should use headline-style capitalization (e.g., "The Best POPL Paper of All Time").
- [x] All levels of headings use headline-style capitalization. Headings "Acknowledgments" and "References" must not be numbered.
- [x] Third-level headings: The heading should be followed by a period and then directly by the text on the same line.
- [x] The title, authors, affiliations, e-mail addresses, all headings, and body text must be in serif font (Libertine). Only the headers must be in sans-serif font (Biolinum).
- [x] Captions of tables and figures must be in upright font face; without horizontal lines between the caption and the body text. The labels must be in bold font. (The LaTeX package 'subfig' interferes with the layout of captions. If this package is used, use '\usepackage[caption=false]{subfig}', which disables the additional caption formatting.)
- [x] Captions: Tables should have their caption above. Figures and listings should have the caption below.
- [x] Colors: ACMART typesets citations and cross-references in color. Please make sure to not change the default color settings (e.g., avoid \hypersetup{draft}).
- [x] Between tables/figures and body text, there must be some vertical white space. Figures must not be framed with an extra box. Please remove those frame boxes.
- [x] Equations and formulas should be typeset and should not be imported as pictures.
- [x] POPL-specific: The sections at the end of the paper should be ordered as follows: first appendices, then acknowledgments, and last references. The acknowledgments and references will not count towards the page limit.
- [x] The first reference must not run into the heading of the references section.
- [x] References: The reference text on the second and following lines should be indented.
- [x] Only for Word users: Text (with links) should be in black, not blue, and not underlined.

If you have any question regarding the proceedings, please contact us by replying to the author-kit e-mail that you have received. 