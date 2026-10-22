export const DURATION = 21 * 1440;
// Day number from 0 to 20 for a time in minutes.
export function dayOf(t) { return Math.min(20, Math.max(0, Math.floor(t / 1440))); }
// Time of day as hours and minutes.
export function clock(t) { const m=Math.floor(Math.max(0,t))%1440; return `${String(Math.floor(m/60)).padStart(2,'0')}:${String(m%60).padStart(2,'0')}`; }
// Index of the last row that starts at or before t, or -1 if none.
export function latestIndex(rows,t) {
  let lo=0,hi=rows.length;
  while(lo<hi){const mid=(lo+hi)>>1;if(rows[mid][0]<=t)lo=mid+1;else hi=mid;}
  return lo-1;
}
// The row that covers time t, if any.
export function activeAt(rows,t) {
  for(let i=latestIndex(rows,t);i>=0;i--){if(rows[i][0]<=t&&t<rows[i][1])return rows[i];}
  return null;
}
// Where a resident is at time t. Trips are straight lines between their end points.
export function positionAt(agent,t) {
  const trip=activeAt(agent.trips,t);
  if(trip){const f=Math.max(0,Math.min(1,(t-trip[0])/Math.max(.001,trip[1]-trip[0])));
    return {lon:trip[2]+(trip[4]-trip[2])*f,lat:trip[3]+(trip[5]-trip[3])*f,kind:'trip',label:`Travelling · ${trip[6]}`,known:true,trip};}
  const activity=activeAt(agent.activities,t);
  if(activity)return {lon:activity[2],lat:activity[3],kind:'activity',label:activity[4].replaceAll('_',' '),area:activity[5],known:true,activity};
  const ai=latestIndex(agent.activities,t),ti=latestIndex(agent.trips,t),a=agent.activities[ai],b=agent.trips[ti];
  if(b&&(!a||b[1]>=a[1]))return {lon:b[4],lat:b[5],kind:'unknown',label:'Last recorded location · activity unknown',known:false};
  if(a)return {lon:a[2],lat:a[3],kind:'unknown',label:'Last recorded location · activity unknown',known:false};
  return null;
}
// Filter records by day, type, search text and time.
export function filterEvents(events,{day,kind='all',query='',pastOnly=false,t=DURATION,allDays=false}) {
  const q=query.trim().toLocaleLowerCase();
  return events.filter(e=>(allDays||dayOf(e.t)===day)&&(kind==='all'||e.kind===kind)&&(!pastOnly||e.t<=t)&&(!q||JSON.stringify(e.record).toLocaleLowerCase().includes(q)));
}
// Display classes for colour. Every native activity label maps to exactly one.
export const ACTIVITY_GROUPS = {
  sleep:'sleep',
  rest_relaxation:'routine',meals:'routine',personal_care:'routine',housework:'routine',
  tv_radio_newspaper_magazines:'routine',childcare:'routine',other:'routine',
  work:'work',schoolwork:'work',learning_self_education:'work',
  social_life:'out',volunteer_social:'out',shopping:'out',medical:'out',sports:'out',hobbies_amusements:'out',
  moving:'travel',commuting:'travel'
};
export const GROUP_NAMES = {sleep:'Sleep',routine:'Routine',work:'Work & study',out:'Out & social',travel:'Travel',unknown:'Unknown'};
// Readable names for activity labels.
const ACTIVITY_NAMES = {
  rest_relaxation:'Rest & relaxation',personal_care:'Personal care',tv_radio_newspaper_magazines:'TV, radio & reading',
  learning_self_education:'Self-education',social_life:'Social life',volunteer_social:'Volunteering',
  hobbies_amusements:'Hobbies & amusements'
};
const MODE_NAMES = {walk:'Walking',bicycle:'Cycling',car:'By car',bus:'By bus',train:'By train'};
const sentence = s => { const text=String(s??'').replaceAll('_',' '); return text.charAt(0).toUpperCase()+text.slice(1); };
// Colour group for an activity label.
export function activityGroup(activity) { return ACTIVITY_GROUPS[activity] ?? 'routine'; }
export function activityName(activity) { return ACTIVITY_NAMES[activity] ?? sentence(activity); }
export function modeName(mode) { return MODE_NAMES[mode] ?? sentence(mode); }
// Colour group for a resident's position.
export function groupAt(p) {
  if(!p||!p.known)return 'unknown';
  return p.kind==='trip'?'travel':activityGroup(p.activity[4]);
}
// Read the resident and time from the URL bookmark, with safe defaults.
export function parseHash(hash) {
  const p=new URLSearchParams(hash.replace(/^#/,''));
  const id=Number(p.get('agent')??0),t=Number(p.get('t')??480);
  return {id:Number.isInteger(id)&&id>=0&&id<50?id:0,t:Number.isFinite(t)?Math.max(0,Math.min(DURATION-.01,t)):480};
}
