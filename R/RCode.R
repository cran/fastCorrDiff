#library(irlba)
#library(plyr)
#library(Matrix)

SS <- function(D,K,K.seq=FALSE,sv=FALSE){
  if(!K.seq){
    SVD <- irlba(A=D,nv=K)
    if(sv){
      R <- SVD$u[,1:K]%*%diag(sqrt(SVD$d[1:K]))
    }else{
      R <- SVD$u[,1:K]
    }
    return(list(R=R,SVD=SVD,score=apply(R,1,function(x){
      return(sqrt(sum(x^2)))
    })))
  }else{
    SVD <- irlba(A=D,nv=K)
    if(K==1){
      R <- matrix(SVD$u,ncol=K)
      R.sv <- matrix(SVD$u*sqrt(SVD$d[1]),ncol=K)
    }else{
      R <- SVD$u[,1:K]
      R.sv <- SVD$u[,1:K]%*%diag(sqrt(SVD$d[1:K]))
    }
    if(sv){
      score <- list()
      for(k in 1:K){
        if(k==1){
          score[[k]] <- abs(R.sv[,1])
        }else{
          score[[k]]  <-  apply(R.sv[,1:k],1,function(x){
            return(sqrt(sum(x^2)))
          })
        }
      }
    }else{
      score <- list()
      for(k in 1:K){
        if(k==1){
          score[[k]] <- abs(R[,1])
        }else{
          score[[k]]  <-  apply(R[,1:k],1,function(x){
            return(sqrt(sum(x^2)))
          })
        }
      }
    }
    
    return(list(R=R,R.sv=R.sv,SVD=SVD,score=score))
  }
}



SS.boot <- function(X1,X2,K,B,sv=FALSE,spearman=FALSE){
  n1 <- ncol(X1)
  n2 <- ncol(X2)
  p <- nrow(X1)
  M <- B
  sim.scores <- matrix(NA,p,M)
  for(k in 1:M){
    print(k)
    tmp.X1 <- X2[,sample(n2,n1,replace=TRUE)]
    tmp.X2 <- X2[,sample(n2,n2,replace=TRUE)]
    if(spearman){
      Y1 <- t(apply(tmp.X1,1,rank))
      Y2 <- t(apply(tmp.X2,1,rank))
    }else{
      Y1 <- tmp.X1
      Y2 <- tmp.X2
    }
    Dtmp <- cor(t(Y1))-cor(t(Y2))
    tmp.SS <- SS(Dtmp,K=K,sv=sv)
    sim.scores[,k] <- tmp.SS$score
    
  }
  return(sim.scores)
}





CaiSpectral <- function(D){
  SVD <- irlba(A=D,nv=1)
  R <- D%*%SVD$u
  return(R)
}



sampling.ER <- function(n,rho){
  m <- ceiling(1.2*n*rho)
  geo.num <- rgeom(m,prob=rho) + 1
  index <- cumsum(geo.num)
  flag <- FALSE
  max.index <- sum(geo.num)
  if(max.index >= n){
    flag <- TRUE
  }
  while(!flag){
    m <- ceiling(0.1*n*rho)
    geo.num <- rgeom(m,prob=rho) + 1
    index <- c(index,cumsum(geo.num) + max.index)
    max.index <- sum(geo.num) + max.index
    if(max.index >= n){
      flag <- TRUE
    }
    
  }
  return(index[index <= n])
}



ind1toind2 <- function(index,nc,nr){
  row.index <- index%%nr
  row.index[row.index==0] <- nr
  col.index <- floor((index-0.01)/nr)+1
  result <- cbind(row.index,col.index)
}

### we will use p x n format: the variables are in rows, observations are in columns.
fast.SS <- function(X1,X2,rho, K,K.seq=FALSE,sv=FALSE,tune=FALSE){
  p <- nrow(X1)
  row.index <- NULL
  if(nrow(X2) != p){
    stop('Different row numbers from the two matrices!')
  }
  n1 <- ncol(X1)
  n2 <- ncol(X2)
  X1 <- X1-rowMeans(X1)
  X2 <- X2-rowMeans(X2)
  
  norm1 <- apply(X1,1,function(x){sqrt(sum(x^2))})
  norm2 <- apply(X2,1,function(x){sqrt(sum(x^2))})
  X1 <- X1/norm1
  X2 <- X2/norm2
  if(tune){
    rho.adjust <- 1-sqrt(1-10*rho/9)
  }else{
    rho.adjust <- 1-sqrt(1-rho)
  }
  sample.index <- sampling.ER(n=p^2,rho=rho.adjust)
  sample.m <- length(sample.index)
  sample.index.mat <- data.frame(ind1toind2(sample.index,nc=p,nr=p))
  names(sample.index.mat) <- c("row.index","col.index")
  id.check <- log(sample.index.mat$row.index+sample.index.mat$col.index)+p*(log(sample.index.mat$row.index)+log(sample.index.mat$col.index))
  id.dup <- duplicated(id.check)
  sample.index.mat <- sample.index.mat[!id.dup,]
  sample.m <- nrow(sample.index.mat)
  unique.sample.row <- unique(sample.index.mat[,1])
  sample.m.row <- length(unique.sample.row)
  sample.row.list <- dlply(sample.index.mat,.(row.index),function(x,X1,X2){
    col.index <- x$col.index
    row.i <- x$row.index[1]
    X1.inner <- X1[col.index,]%*%matrix(X1[row.i,],ncol=1)
    X2.inner <- X2[col.index,]%*%matrix(X2[row.i,],ncol=1)
    return(list(row.index=row.i,col.index=col.index,D.value=X1.inner-X2.inner))
  },X1,X2)
  if(tune){
    holdout.index <- sample(1:sample.m,size=floor(0.1*sample.m))
    train.index <- seq(1,sample.m)[-holdout.index]
    full.D.j <- unlist(lapply(sample.row.list,function(x)return(x$col.index)))
    full.D.i <- unlist(lapply(sample.row.list,function(x)return(rep(x$row.index,length(x$col.index)))))
    full.D.val <- unlist(lapply(sample.row.list,function(x)return(x$D.value)))
    D.j <- full.D.j[train.index]
    D.i <- full.D.i[train.index]
    D.val <- full.D.val[train.index]
    sp.D <- sparseMatrix(i=D.i,j=D.j,x=D.val,dims=c(p,p))
    sp.D <- sp.D + t(sp.D)
    sp.D <- sp.D/rho
    diag(sp.D) <- 1
    SS.result <- SS(D=sp.D,K=K,K.seq=K.seq,sv=sv)
    Cai.result <- CaiSpectral(sp.D)
    T1 <- Sys.time()
    print("begin hold out evaluation...")
    hold.out.m <- length(holdout.index)
    R.sv.hold.out.i <- SS.result$R.sv[full.D.i[holdout.index],]
    R.sv.hold.out.j <- SS.result$R.sv[full.D.j[holdout.index],]
    R.sv.hold.out.comp <- R.sv.hold.out.i*R.sv.hold.out.j
    hold.out.pred.seq <- t(apply(R.sv.hold.out.comp,1,cumsum))
    #hold.out.pred.seq[hold.out.pred.seq< -1] <- -1
    #hold.out.pred.seq[hold.out.pred.seq> 1] <- 1
    #print(dim(hold.out.pred.seq))
    hold.out.error <- colMeans((hold.out.pred.seq-full.D.val[holdout.index])^2)
    #plot(hold.out.error)
    hold.out.error <- apply(abs(hold.out.pred.seq-full.D.val[holdout.index]),2,mean)
    hold.out.error[1] <- max(hold.out.error)
    T2 <- Sys.time()
    tune.time <- as.numeric(T2-T1)
    #plot(1:K,hold.out.error)
    #plot(abs(colMeans((hold.out.pred.seq)) - mean((full.D.val[holdout.index]))))
    return(list(SS=SS.result,Cai=Cai.result,tune.error=hold.out.error,tune.time=tune.time))
  }else{
    D.j <- unlist(lapply(sample.row.list,function(x)return(x$col.index)))
    D.i <- unlist(lapply(sample.row.list,function(x)return(rep(x$row.index,length(x$col.index)))))
    D.val <- unlist(lapply(sample.row.list,function(x)return(x$D.value)))
    sp.D <- sparseMatrix(i=D.i,j=D.j,x=D.val,dims=c(p,p))
    sp.D <- sp.D + t(sp.D)
    diag(sp.D) <- 1
    SS.result <- SS(D=sp.D,K=K,K.seq=K.seq,sv=sv)
    Cai.result <- CaiSpectral(sp.D)
    return(list(SS=SS.result,Cai=Cai.result))
  }
}

## calculate sqrt for PD matrix - there are small numerical errors
psd.sqrt <- function(X,inv=FALSE,K=NULL){
  n <- nrow(X)
  if(is.null(K)){
    K <- n
  }
  if(ncol(X)!=n) warning("dimension problem")
  Eig <- eigs_sym(X,k=K)
  if(sum(Eig$values<0)>0) warning("not psd")
  if(inv){
    R <- Eig$vectors %*% (t(Eig$vectors)/sqrt(Eig$values))
  }else{
    R <- Eig$vectors %*% (t(Eig$vectors)*sqrt(Eig$values))
  }
  #O <- Eig$vectors %*% t(Eig$vectors*Eig$values)
  return(R)
}






### we will use p x n format: the variables are in rows, observations are in columns. This is a function to quickly sample some pairs and get their correlation values
fast.Correlation <- function(X1,rho){
  p <- nrow(X1)
  n1 <- ncol(X1)
  X1 <- X1-rowMeans(X1)
  rho.adjust <- 1-sqrt(1-rho)
  row.index <- NULL
  
  norm1 <- apply(X1,1,function(x){sqrt(sum(x^2))})
  X1 <- X1/norm1
  sample.index <- sampling.ER(n=p^2,rho=rho.adjust)
  sample.m <- length(sample.index)
  sample.index.mat <- data.frame(ind1toind2(sample.index,nc=p,nr=p))
  names(sample.index.mat) <- c("row.index","col.index")
  id.check <- log(sample.index.mat$row.index+sample.index.mat$col.index)+p*(log(sample.index.mat$row.index)+log(sample.index.mat$col.index))
  id.dup <- duplicated(id.check)
  sample.index.mat <- sample.index.mat[!id.dup,]
  sample.m <- nrow(sample.index.mat)
  unique.sample.row <- unique(sample.index.mat[,1])
  sample.m.row <- length(unique.sample.row)
  sample.row.list <- dlply(sample.index.mat,.(row.index),function(x,X1,X2){
    col.index <- x$col.index
    row.i <- x$row.index[1]
    X1.inner <- X1[col.index,]%*%matrix(X1[row.i,],ncol=1)
    return(list(row.index=row.i,col.index=col.index,D.value=X1.inner))
  },X1)
  
 return(sample.row.list)
  
}

