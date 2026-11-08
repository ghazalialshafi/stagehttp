// keep-alive HTTP load generator: epoll, C conns, pipeline depth P, T seconds
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
typedef struct { int fd; char buf[16384]; int len; int pending; } Conn;
static double now(){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(int argc,char**argv){
  int port=atoi(argv[1]), C=atoi(argv[2]), P=atoi(argv[3]); double T=atof(argv[4]);
  const char*path=argc>5?argv[5]:"/hello";
  char req[256]; int rl=snprintf(req,256,"GET %s HTTP/1.1\r\nHost: x\r\nUser-Agent: bench\r\nAccept: */*\r\n\r\n",path);
  char *batch=malloc(rl*P); for(int i=0;i<P;i++) memcpy(batch+i*rl,req,rl);
  int ep=epoll_create1(0); Conn*cs=calloc(C,sizeof(Conn));
  struct sockaddr_in a={0}; a.sin_family=AF_INET;a.sin_port=htons(port);inet_pton(AF_INET,"127.0.0.1",&a.sin_addr);
  for(int i=0;i<C;i++){int fd=socket(AF_INET,SOCK_STREAM,0);
    if(connect(fd,(void*)&a,sizeof a)<0){perror("connect");return 1;}
    int one=1;setsockopt(fd,IPPROTO_TCP,TCP_NODELAY,&one,sizeof one);fcntl(fd,F_SETFL,O_NONBLOCK);
    cs[i].fd=fd;struct epoll_event e={.events=EPOLLIN,.data.ptr=&cs[i]};epoll_ctl(ep,EPOLL_CTL_ADD,fd,&e);
    write(fd,batch,rl*P);cs[i].pending=P;}
  long done=0; double t0=now(),end=t0+T; struct epoll_event evs[256];
  while(now()<end){int n=epoll_wait(ep,evs,256,100);
    for(int k=0;k<n;k++){Conn*c=evs[k].data.ptr;
      int r=read(c->fd,c->buf+c->len,sizeof(c->buf)-c->len-1); if(r<=0){if(errno==EAGAIN)continue;fprintf(stderr,"conn closed\n");return 2;}
      c->len+=r;c->buf[c->len]=0; int off=0,got=0;
      for(;;){char*h=memmem(c->buf+off,c->len-off,"\r\n\r\n",4); if(!h)break;
        int hl=(h-(c->buf+off))+4; int cl=0; char*p=memmem(c->buf+off,hl,"Content-Length: ",16); if(!p)p=memmem(c->buf+off,hl,"content-length: ",16);
        if(p)cl=atoi(p+16); if(c->len-off<hl+cl)break; off+=hl+cl;got++;}
      if(off){memmove(c->buf,c->buf+off,c->len-off);c->len-=off;}
      if(got){done+=got;c->pending-=got; if(c->pending==0){write(c->fd,batch,rl*P);c->pending=P;}}
    }}
  double el=now()-t0; printf("%-28s conns=%d pipe=%d  %.0f req/s\n",argv[0]+0,C,P,done/el); return 0;}
