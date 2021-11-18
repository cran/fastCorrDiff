\name{fast.SS}
\alias{fast.SS}
\title{
Compressed spectral screening}
\description{
Compressed spectral screening for high-dimensional differential correlation matrices.
}
\usage{
fast.SS(X1, X2, rho, K, K.seq = FALSE, sv = FALSE, tune = FALSE)
}
\arguments{
  \item{X1}{
Matrix of the first group of observations. Each row is variable and each column is an observation. Note that this is different from the usual way of statistical data matrices, because usually number of variables is much larger than the number of observations in this case.
}
  \item{X2}{
Matrix of the second group of observations. Each row is variable and each column is an observation. Note that this is different from the usual way of statistical data matrices, because usually number of variables is much larger than the number of observations in this case.
}
  \item{rho}{
The sampling proportion for compressed screening. 
}
  \item{K}{
The rank K or the maximum rank K to calculate the spectral scores
}
  \item{K.seq}{
logical value. If TRUE, then it returns the spectral screening scores for all rank from 1 to K. If FALSE (default), it returns the rank K result
}
  \item{sv}{
logical value. If TRUE, the square roots of singular values will be used in the score calculation. 
}
  \item{tune}{
logical value. If TRUE, a cross-validation procedure will be called to estimate the the rank K by evaluating imputation errors of ten percent of additional sampled entries. 
}
}
\details{
This function can be used to tune the SS function as well. Also, the spectral projection method of Cai et al (2017) is also implemented as part of the function. So, it will return the scores by both compressed version of spectral screening and spectral projection. Notice that if one wants to analyze the Spearman's correlation, the input objects X1 and X2 should be the rank matrices instead of raw data matrices.
}
\value{
  \item{SS }{The result of the SS function on the incomplete correlation matrix}
  \item{Cai }{The result of the spectral projection of Cai et al (2017) on the incomplete correlation matrix}
  \item{tune.error }{The imputation error on hold-out entries}
\item{tune.time}{Timing for the additional tuning step.}
  
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

fit <- fast.SS(X1, X2, 0.3, K=2) 
fit$SS$score

}
