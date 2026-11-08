// theoretical floor: minimal single-threaded epoll ET HTTP server in C, same response bytes
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
static const char R[]="HTTP/1.1 200 OK\r\nDate: Sun, 08 Nov 2026 02:04:26 GMT\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 13\r\n\r\nHello, World!";
int main(int argc,char**argv){
  int port=argc>1?atoi(argv[1]):8090;
  int l=socket(AF_INET,SOCK_STREAM|SOCK_NONBLOCK,0);int one=1;setsockopt(l,SOL_SOCKET,SO_REUSEADDR,&one,4);
  setsockopt(l,IPPROTO_TCP,TCP_NODELAY,&one,4);
  struct sockaddr_in a={0};a.sin_family=AF_INET;a.sin_port=htons(port);
  bind(l,(void*)&a,sizeof a);listen(l,1024);
  int ep=epoll_create1(0);struct epoll_event e={.events=EPOLLIN|EPOLLET,.data.fd=l};epoll_ctl(ep,EPOLL_CTL_ADD,l,&e);
  struct epoll_event ev[256];char buf[65536];
  for(;;){int n=epoll_wait(ep,ev,256,-1);
    for(int i=0;i<n;i++){int fd=ev[i].data.fd;
      if(fd==l){for(;;){int c=accept4(l,0,0,SOCK_NONBLOCK);if(c<0)break;struct epoll_event ce={.events=EPOLLIN|EPOLLET|EPOLLRDHUP,.data.fd=c};epoll_ctl(ep,EPOLL_CTL_ADD,c,&ce);}continue;}
      for(;;){int r=recv(fd,buf,sizeof buf,0);if(r<=0){if(r==0||errno!=EAGAIN)close(fd);break;}
        // naive: one response per recv (no pipelining)
        send(fd,R,sizeof R-1,MSG_NOSIGNAL); if(r<(int)sizeof buf)break;}
    }}}
