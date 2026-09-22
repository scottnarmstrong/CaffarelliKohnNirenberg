# Mathematical sources

The references below are the bibliography of [the source paper](../paper/ckn.tex),
with citation keys from [refs.bib](../paper/refs.bib). They include the original
partial-regularity theorem, subsequent proof routes and corrections, and supporting
analysis. Inclusion here does not mean that every result in a reference is a
formalized dependency. The adopted mathematical scope and departures are recorded
in [DEVIATIONS.md](DEVIATIONS.md) and [the design notes](DESIGN_NOTES.md).

Lin's 1998 paper supplies pressure estimates. The manuscript follows the
direct-iteration organization of Kukavica and Lemarié-Rieusset, combined
with O'Leary's Morrey and potential estimates; it does not formalize Lin's
compactness argument. The mathematical conventions and differences are
described in [DEVIATIONS.md](DEVIATIONS.md) and
[DESIGN_NOTES.md](DESIGN_NOTES.md).

DOIs were checked against publisher or publisher-deposited Crossref metadata on
2026-09-20–22. Journal citations give article page ranges; book citations give numbered
text extents where available. Original publication years are retained when a DOI
identifies a later electronic release of the same book. An unconfirmed identifier
is marked explicitly rather than replaced by a DOI for a review or another edition.

## Primary proof sources

- **Wolf, Jörg.** “A direct proof of the Caffarelli–Kohn–Nirenberg theorem.” *Banach Center Publications* **81**, 533–552 (2008). Institute of Mathematics, Polish Academy of Sciences. [EuDML record](https://eudml.org/doc/282308), [DOI: 10.4064/bc81-0-34](https://doi.org/10.4064/bc81-0-34), zbMATH 1154.35426. Direct proof with a criterion on the vorticity component perpendicular to velocity. Key: `Wolf2008`.

- **Robinson, James C.; Rodrigo, José L.; Sadowski, Witold.** *The Three-Dimensional Navier–Stokes Equations: Classical Theory*. Cambridge Studies in Advanced Mathematics **157**. Cambridge University Press, Cambridge, 2016, Chapters 15–16. [Cambridge book record and DOI: 10.1017/CBO9781139095143](https://doi.org/10.1017/CBO9781139095143). Key: `RobinsonRodrigoSadowski2016`.

- **Caffarelli, Luis; Kohn, Robert; Nirenberg, Louis.** “Partial regularity of suitable weak solutions of the Navier–Stokes equations.” *Communications on Pure and Applied Mathematics* **35**(6), 771–831 (1982). [DOI: 10.1002/cpa.3160350604](https://doi.org/10.1002/cpa.3160350604). Original theorem. Bibliography key: `CKN1982`.

- **Lin, Fanghua.** “A new proof of the Caffarelli–Kohn–Nirenberg theorem.” *Communications on Pure and Applied Mathematics* **51**(3), 241–257 (1998). [DOI: 10.1002/(SICI)1097-0312(199803)51:3<241::AID-CPA2>3.0.CO;2-A](https://doi.org/10.1002/%28SICI%291097-0312%28199803%2951%3A3%3C241%3A%3AAID-CPA2%3E3.0.CO%3B2-A). Pressure-estimate source; its compactness argument is outside the formalized proof route. Key: `Lin1998`.

- **Ladyzhenskaya, Olga A.; Seregin, Gregory A.** “On partial regularity of suitable weak solutions to the three-dimensional Navier–Stokes equations.” *Journal of Mathematical Fluid Mechanics* **1**(4), 356–387 (1999). [DOI: 10.1007/s000210050015](https://doi.org/10.1007/s000210050015). Suitable-solution and partial-regularity treatment used in the paper's comparison and corrections. Key: `LadyzhenskayaSeregin1999`.

- **Kukavica, Igor.** “On partial regularity for the Navier–Stokes equations.” *Discrete and Continuous Dynamical Systems* **21**(3), 717–728 (2008). [DOI: 10.3934/dcds.2008.21.717](https://doi.org/10.3934/dcds.2008.21.717). Direct scale iteration and force-dependent regularity estimates. Key: `Kukavica2008`.

- **Lemarié-Rieusset, Pierre Gilles.** *Recent Developments in the Navier–Stokes Problem*. Chapman & Hall/CRC Research Notes in Mathematics, **431**. Chapman & Hall/CRC, Boca Raton, 2002, 393 pp. [DOI: 10.1201/9780367801656](https://doi.org/10.1201/9780367801656). Key: `LemarieRieusset2002`.

- **Lemarié-Rieusset, Pierre Gilles.** *The Navier–Stokes Problem in the 21st Century*. First edition. CRC Press, Boca Raton, 2016, 718 pp. [DOI: 10.1201/b19556](https://doi.org/10.1201/b19556). Sections 13.8–13.9 supply the paper's four-step architecture: energy/pressure estimates, Morrey iteration, improvement of integrability, and Hölder regularity. This citation is to the 2016 edition, not the 2024 second edition. Key: `LemarieRieusset2016`.

## Supporting treatments and analysis

- **Tsai, Tai-Peng.** *Lectures on Navier–Stokes Equations*. Graduate Studies in Mathematics, **192**. American Mathematical Society, Providence, RI, 2018, 224 pp. [DOI: 10.1090/gsm/192](https://doi.org/10.1090/gsm/192). Key: `Tsai2018`.

- **Scheffer, Vladimir.** “Hausdorff measure and the Navier–Stokes equations.” *Communications in Mathematical Physics* **55**(2), 97–112 (1977). [DOI: 10.1007/BF01626512](https://doi.org/10.1007/BF01626512). Key: `Scheffer1977`.

- **Vasseur, Alexis F.** “A new proof of partial regularity of solutions to Navier–Stokes equations.” *NoDEA: Nonlinear Differential Equations and Applications* **14**(5–6), 753–785 (2007). [DOI: 10.1007/s00030-007-6001-4](https://doi.org/10.1007/s00030-007-6001-4). Key: `Vasseur2007`.

- **O'Leary, Mike.** “Conditions for the local boundedness of solutions of the Navier–Stokes system in three dimensions.” *Communications in Partial Differential Equations* **28**(3–4), 617–636 (2003). [DOI: 10.1081/PDE-120020490](https://doi.org/10.1081/PDE-120020490). Source for the local Morrey/potential regularity route. Key: `OLeary2003`.

- **Colombo, Maria; De Lellis, Camillo; Massaccesi, Annalisa.** “The generalized Caffarelli–Kohn–Nirenberg theorem for the hyperdissipative Navier–Stokes system.” *Communications on Pure and Applied Mathematics* **73**(3), 609–663 (2020). [DOI: 10.1002/cpa.21865](https://doi.org/10.1002/cpa.21865). The bibliography key `ColomboDeLellisMassaccesi2018` is retained for traceability; the journal publication year is **2020**, with online publication in 2019 and preprint [arXiv:1712.07015](https://arxiv.org/abs/1712.07015).

- **Adams, David R.** “A note on Riesz potentials.” *Duke Mathematical Journal* **42**(4), 765–778 (1975). [DOI: 10.1215/S0012-7094-75-04265-9](https://doi.org/10.1215/S0012-7094-75-04265-9). Key: `Adams1975`.

- **Stein, Elias M.** *Singular Integrals and Differentiability Properties of Functions*. Princeton Mathematical Series, **30**. Princeton University Press, Princeton, NJ, 1970, 290 pp. [DOI: 10.1515/9781400883882](https://doi.org/10.1515/9781400883882). Key: `Stein1970`.

- **Stein, Elias M.**, with the assistance of **Timothy S. Murphy**. *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory Integrals*. Princeton Mathematical Series, **43**. Princeton University Press, Princeton, NJ, 1993, 695 pp. [DOI: 10.1515/9781400883929](https://doi.org/10.1515/9781400883929). Key: `Stein1993`.

- **Gilbarg, David; Trudinger, Neil S.** *Elliptic Partial Differential Equations of Second Order*. Second edition, Classics in Mathematics reprint. Springer, Berlin–Heidelberg, 2001, xiii + 518 pp. [DOI: 10.1007/978-3-642-61798-0](https://doi.org/10.1007/978-3-642-61798-0). The earlier edition appeared as Grundlehren der mathematischen Wissenschaften **224**; the cited 2001 reprint is in Classics in Mathematics. Key: `GilbargTrudinger2001`.

- **Ladyzhenskaya, Olga A.; Solonnikov, Vsevolod A.; Ural'tseva, Nina N.** *Linear and Quasilinear Equations of Parabolic Type*. Translations of Mathematical Monographs, **23**. American Mathematical Society, Providence, RI, 1968, xi + 648 pp. [DOI: 10.1090/mmono/023](https://doi.org/10.1090/mmono/023). The publisher's title uses “Quasi-linear”; author-name transliterations also vary across catalogues. Key: `LadyzhenskayaSolonnikovUraltseva1968`.

- **Giaquinta, Mariano.** *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic Systems*. Annals of Mathematics Studies, **105**. Princeton University Press, Princeton, NJ, 1983, vii + 297 pp. [DOI: 10.1515/9781400881628](https://doi.org/10.1515/9781400881628) (whole-book electronic release). Key: `Giaquinta1983`.

- **Mattila, Pertti.** *Geometry of Sets and Measures in Euclidean Spaces: Fractals and Rectifiability*. Cambridge Studies in Advanced Mathematics, **44**. Cambridge University Press, Cambridge, 1995, 343 pp. [DOI: 10.1017/CBO9780511623813](https://doi.org/10.1017/CBO9780511623813). Key: `Mattila1995`.

- **Temam, Roger.** *Navier–Stokes Equations: Theory and Numerical Analysis*. Studies in Mathematics and its Applications, **2**. North-Holland, Amsterdam, 1977, 500 pp. [DOI: 10.1016/S0168-2024(09)X7004-9](https://doi.org/10.1016/S0168-2024(09)X7004-9). Crossref supplies the matching title and 1977 date, with publisher Elsevier and ISBN 9780720428407; the deposited author field is empty. Key: `Temam1977`.

- **Diestel, Joseph; Uhl, J. Jerry, Jr.** *Vector Measures*. Mathematical Surveys, **15**. American Mathematical Society, Providence, RI, 1977, xiii + 322 pp. [DOI: 10.1090/surv/015](https://doi.org/10.1090/surv/015). The current publisher catalogue calls the series Mathematical Surveys and Monographs. Key: `DiestelUhl1977`.

- **Simon, Jacques.** “Compact sets in the space $L^p(0,T;B)$.” *Annali di Matematica Pura ed Applicata* **146**, 65–96 (1987). [DOI: 10.1007/BF01762360](https://doi.org/10.1007/BF01762360). Corollary 4 supplies the Aubin–Lions compactness statement and time-continuity endpoint recorded in `ext:aubin-lions`; this input is not used by the direct proof formalized here. Key: `Simon1987`.
