#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
int main(int c,char**v){int port=atoi(v[1]);double T=atof(v[2]);
 const char*rq="GET /hello HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";char b[4096];long n=0;
 struct sockaddr_in a={0};a.sin_family=AF_INET;a.sin_port=htons(port);inet_pton(AF_INET,"127.0.0.1",&a.sin_addr);
 struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);
 for(;;){int f=socket(AF_INET,SOCK_STREAM,0);if(connect(f,(void*)&a,sizeof a)<0){perror("c");return 1;}
  write(f,rq,strlen(rq));while(read(f,b,sizeof b)>0);close(f);n++;
  clock_gettime(CLOCK_MONOTONIC,&t1);double e=(t1.tv_sec-t0.tv_sec)+(t1.tv_nsec-t0.tv_nsec)*1e-9;if(e>T){printf("churn %.0f conn/s\n",n/e);return 0;}}}
