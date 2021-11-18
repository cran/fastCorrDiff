\name{sampling.ER}
\alias{sampling.ER}
\alias{psd.sqrt}
\alias{ind1toind2}
\title{
Internal functions for intermediate computation
}
\description{
Internal functions for intermediate computation
}
\usage{
sampling.ER(n, rho)
psd.sqrt(X, inv = FALSE, K = NULL)
ind1toind2(index, nc, nr)
fast.Correlation(X1, rho)

}
\arguments{
  \item{n}{
number of total length of indices
}
  \item{rho}{
  sampling probability
}
  \item{X}{
  Matrix to for which square root matrix is calculated
}
  \item{inv}{
  Whether to calculate its inverse sqrt
}
  \item{K}{
  Rank K is low-rank approximation is desired 
}
  \item{index}{
  vector index
}
  \item{nc}{
  number of columns
}
  \item{index}{
  number of rows
}
  \item{X1}{
Matrix of the first group of observations. Each row is variable and each column is an observation. Note that this is different from the usual way of statistical data matrices, because usually number of variables is much larger than the number of observations in this case.
}

}
\references{
Tianxi Li, Xiwei Tang, and Ajay Chatrath. Compressed spectral screening for large-scale differential correlation analysis with application in selecting Glioblastoma gene modules. arXiv preprint arXiv:2111.03721, 2021.
}
\author{
Tianxi Li and Xiwei Tang
Maintainer: Tianxi Li  \email{tianxili@virginia.edu}
}
 \keyword{ internal }
