\name{fastCorrDiff-package}
\alias{fastCorrDiff-package}
\alias{fastCorrDiff}
\docType{package}
\title{
\packageTitle{fastCorrDiff}
}
\description{
\packageDescription{fastCorrDiff}
}
\details{

The DESCRIPTION file:
\packageDESCRIPTION{fastCorrDiff}
\packageIndices{fastCorrDiff}
The package for fast differential correlation/covariance analysis based on spectral methods. It includes the spectral screening and compressed spectral screening methods proposed in Li et al (2021) <arXiv:2111.03721> to identify a group of variables exhibiting differential correlation pattern between two settings.The methods are designed for a great scalability when the number of variables is large, such that computing the full correlation matrices is not feasible.
}
\author{
\packageAuthor{fastCorrDiff}

Maintainer: \packageMaintainer{fastCorrDiff}
}
\references{
Tianxi Li, Xiwei Tang, and Ajay Chatrath. Compressed spectral screening for large-scale differential correlation analysis with application in selecting Glioblastoma gene modules. arXiv preprint arXiv:2111.03721, 2021.

T. T. Cai, T. Liang, A. Rakhlin, et al. Computational and statistical boundaries for submatrix localization
in a large noisy matrix. The Annals of Statistics, 45(4):1403-1430, 2017.
}
\keyword{ package }
\examples{

X1 <- matrix(rnorm(200),10,20)
C1 <- cor(X1)
X2 <- matrix(rnorm(200),10,20)
C2 <- cor(X2)

D <- C1-C2

fit <- SS(D, 3, K.seq = FALSE, sv = FALSE)

fit$score
}
