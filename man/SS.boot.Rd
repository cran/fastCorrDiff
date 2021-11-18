\name{SS.boot}
\alias{SS.boot}
\title{
Bootstraping function for spectral screening
}
\description{
The function initialize a bootstraping procedure for spectral score calculation, which can be used to determine a threshold for SS selection.
}
\usage{
SS.boot(X1, X2, K, B, sv = FALSE, spearman = FALSE)
}
\arguments{
  \item{X1}{
Matrix of the first group of observations. Each row is variable and each column is an observation. Note that this is different from the usual way of statistical data matrices, because usually number of variables is much larger than the number of observations in this case.
}
  \item{X2}{
Matrix of the second group of observations. Each row is variable and each column is an observation. Note that this is different from the usual way of statistical data matrices, because usually number of variables is much larger than the number of observations in this case.
}
  \item{K}{
Rank K in spectral screening
}
  \item{B}{
Number of bootstrap samples
}
  \item{sv}{
logical value. If TRUE, the square roots of singular values will be used in the score calculation. 
}
  \item{spearman}{
logical value. If TRUE, Spearman's correlation is used. Otherwise (default), the calculation is based on Pearson's correlation.
}
}
\details{
See the details in the reference paper.
}
\value{
A matrix with B columns. Each column is a bootstraped score for the p variables. 
}
\references{
Tianxi Li, Xiwei Tang, and Ajay Chatrath. Compressed spectral screening for large-scale differential correlation analysis with application in selecting Glioblastoma gene modules. arXiv preprint arXiv:2111.03721, 2021.
}
\author{
Tianxi Li and Xiwei Tang
Maintainer: Tianxi Li  \email{tianxili@virginia.edu}
}
\seealso{
\code{\link{SS}}
}
\examples{

X1 <- matrix(rnorm(200),10,20)
X2 <- matrix(rnorm(200),10,20)


bt <- SS.boot(X1,X2,3, 10)

}
