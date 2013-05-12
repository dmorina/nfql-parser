import os
import subprocess
all=6
count=0


file1=subprocess.check_output('$ENGINE/engine tests/json/query-dns-udp.json tests/trace-2012.ftz -v 1 | grep "No. of Filtered Records:"',shell=True)
file2=subprocess.check_output('$ENGINE/engine output/query-dns-udp-parsed.json tests/trace-2012.ftz -v 1| grep "No. of Filtered Records:"',shell=True)
if (file1==file2):
    count=count+1
    print("DNS-UDP: OK!")

file3=subprocess.check_output('$ENGINE/engine tests/json/query-http-octets.json tests/trace-2012.ftz -v 1 | grep "No. of Filtered Records:"',shell=True)
file4=subprocess.check_output('$ENGINE/engine output/query-http-octets-parsed.json tests/trace-2012.ftz -v 1| grep "No. of Filtered Records:"',shell=True)
if (file3==file4):
    count=count+1
    print("HTTP-OCTETS: OK!")

file5=subprocess.check_output('$ENGINE/engine tests/json/query-https-tcp-session.json tests/trace-2012.ftz -v 1 | grep "No. of Filtered Records:"',shell=True)
file6=subprocess.check_output('$ENGINE/engine output/query-https-tcp-session-parsed.json tests/trace-2012.ftz -v 1| grep "No. of Filtered Records:"',shell=True)
if (file5==file6):
    count=count+1
    print("HTTPS-TCP: OK!")
file7=subprocess.check_output('$ENGINE/engine tests/json/query-http-tcp-session.json tests/trace-2012.ftz -v 1 | grep "No. of Filtered Records:"',shell=True)
file8=subprocess.check_output('$ENGINE/engine output/query-http-tcp-session-parsed.json tests/trace-2012.ftz -v 1| grep "No. of Filtered Records:"',shell=True)
if (file7==file8):
    count=count+1
    print("HTTP-TCP: OK!")

file9=subprocess.check_output('$ENGINE/engine tests/json/query-mdns-udp.json tests/trace-2012.ftz -v 1 | grep "No. of Filtered Records:"',shell=True)
file10=subprocess.check_output('$ENGINE/engine output/query-mdns-udp-parsed.json tests/trace-2012.ftz -v 1| grep "No. of Filtered Records:"',shell=True)
if (file9==file10):
    count=count+1
    print("MDNS-UDP: OK!")

file11=subprocess.check_output('$ENGINE/engine tests/json/query-tcp-session.json tests/trace-2012.ftz -v 1 | grep "No. of Filtered Records:"',shell=True)
file12=subprocess.check_output('$ENGINE/engine output/query-tcp-session-parsed.json tests/trace-2012.ftz -v 1| grep "No. of Filtered Records:"',shell=True)
if (file11==file12):
    count=count+1
    print("TCP: OK!")

print('Tests passed %s/%s'%(count,all))

