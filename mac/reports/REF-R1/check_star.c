#include <Accelerate/Accelerate.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

/* Numerical check only: each edge term is the rank-nine spin-4 projector.
   Basis digits k=0,...,4 encode magnetic quantum numbers k-2.
   Clebsch--Gordan coefficients of the maximal-spin summand are
   sqrt(binomial(4,k1)*binomial(4,k2)/binomial(8,k1+k2)). */
int main(void) {
    const int c4[5] = {1,4,6,4,1};
    const int c8[9] = {1,8,28,56,70,56,28,8,1};
    const int pow5[5] = {1,5,25,125,625};
    int digits[3125][5], total[3125];
    int zeros=0, npositive=0;
    double gap=10.0, maxres=0.0;
    for (int s=0;s<3125;s++) {
        total[s]=0;
        for (int p=0;p<5;p++) {
            digits[s][p]=(s/pow5[p])%5;
            total[s]+=digits[s][p];
        }
    }
    for (int M=0;M<=20;M++) {
        int states[3125], index[3125], n=0;
        for(int s=0;s<3125;s++) {
            index[s]=-1;
            if(total[s]==M) { index[s]=n; states[n++]=s; }
        }
        double *h=calloc((size_t)n*n,sizeof(double));
        double *eval=calloc(n,sizeof(double));
        for(int j=0;j<n;j++) {
            int s=states[j], a=digits[s][0];
            for(int leaf=1;leaf<=4;leaf++) {
                int b=digits[s][leaf], sum=a+b;
                for(int ap=0;ap<=4;ap++) {
                    int bp=sum-ap;
                    if(bp<0 || bp>4) continue;
                    int sp=s+(ap-a)*pow5[0]+(bp-b)*pow5[leaf];
                    int i=index[sp];
                    h[i+(size_t)n*j]+=sqrt((double)c4[a]*c4[b]*c4[ap]*c4[bp])/c8[sum];
                }
            }
        }
        for(int i=0;i<n;i++) for(int j=0;j<n;j++) {
            double err=fabs(h[i+(size_t)n*j]-h[j+(size_t)n*i]);
            if(err>maxres) maxres=err;
        }
        __CLPK_integer nn=n, lda=n, info=0, lwork=-1;
        double query;
        char job='N', uplo='U';
        dsyev_(&job,&uplo,&nn,h,&lda,eval,&query,&lwork,&info);
        lwork=(__CLPK_integer)query;
        double *work=calloc(lwork,sizeof(double));
        dsyev_(&job,&uplo,&nn,h,&lda,eval,work,&lwork,&info);
        if(info) { fprintf(stderr,"LAPACK error %d\n",(int)info); return 1; }
        double sector_gap=10.0;
        int sector_zeros=0;
        for(int i=0;i<n;i++) {
            if(fabs(eval[i])<1e-10) { zeros++; sector_zeros++; }
            else {
                npositive++;
                if(eval[i]<gap) gap=eval[i];
                if(eval[i]<sector_gap) sector_gap=eval[i];
            }
        }
        printf("M=%d dim=%d zero=%d min_positive=%.15g\n",M-10,n,sector_zeros,sector_gap);
        free(work);free(h);free(eval);
    }
    printf("Numerical star gap %.15g; kernel dimension %d; positive dimension %d; symmetry residual %.3g\n",gap,zeros,npositive,maxres);
    return 0;
}
